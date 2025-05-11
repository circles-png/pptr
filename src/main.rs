#![allow(clippy::fallible_impl_from, clippy::too_many_lines)]

use std::{
    env::args,
    fmt::{self, Debug, Display, Formatter},
    fs::read_to_string,
    iter::{Empty, empty, once, zip},
    ops::Not,
};

use convert_case::{Case, Casing};
use itertools::{Either, Itertools};
use rustpython_parser::{
    Mode,
    ast::{BoolOp, CmpOp, Constant, Expr, Operator, Stmt, UnaryOp},
    lexer::lex,
    parse_tokens,
    text_size::TextRange,
};
use tap::Pipe;

#[derive(Debug)]
struct Psuedocode {
    statements: Vec<Statement>,
}

#[derive(Debug)]
enum Statement {
    Comment {
        content: String,
    },
    Process {
        name: String,
        args: Vec<String>,
        body: Vec<Statement>,
    },
    Input {
        out: String,
    },
    ForNext {
        variable: String,
        from: String,
        to: String,
        step: String,
        body: Vec<Statement>,
    },
    Assignment {
        left: String,
        right: String,
    },
    If {
        condition: String,
        body: Vec<Statement>,
        else_body: Option<Vec<Statement>>,
    },
    Return(Option<String>),
    While {
        condition: String,
        body: Vec<Statement>,
    },
    Display(String),
    Other(String),
}

impl Statement {
    fn transpile_assign(
        targets: Vec<Expr<TextRange>>,
        value: Box<Expr<TextRange>>,
    ) -> impl Iterator<Item = Self> {
        targets
            .iter()
            .exactly_one()
            .ok()
            .and_then(Expr::as_name_expr)
            .map(|name| name.id.to_string())
            .filter(|_| {
                value.as_call_expr().is_some_and(|call| {
                    call.func
                        .as_name_expr()
                        .is_some_and(|name| ["int"].contains(&&*name.id))
                        && call
                            .args
                            .iter()
                            .exactly_one()
                            .unwrap()
                            .as_call_expr()
                            .is_some_and(|call| {
                                call.func
                                    .as_name_expr()
                                    .is_some_and(|name| *name.id == *"input")
                            })
                })
            })
            .map_or_else(
                || {
                    let left = targets.into_iter().exactly_one().unwrap();
                    if left.is_tuple_expr() {
                        let left = left.expect_tuple_expr();
                        zip(left.elts, value.expect_tuple_expr().elts)
                            .map(|(left, right)| Self::Assignment {
                                left: expr_to_string(&left),
                                right: expr_to_string(&right),
                            })
                            .pipe(Either::Left)
                    } else {
                        Self::Assignment {
                            left: expr_to_string(&left),
                            right: expr_to_string(&value),
                        }
                        .pipe(once)
                        .pipe(Either::Right)
                    }
                    .pipe(Either::Right)
                },
                |out| Self::Input { out }.pipe(once).pipe(Either::Left),
            )
    }
    fn transpile(statement: Stmt) -> impl Iterator<Item = Self> {
        match statement {
            Stmt::FunctionDef(function_def) => Self::Process {
                name: function_def.name.to_string().to_case(Case::Pascal),
                args: function_def
                    .args
                    .args
                    .into_iter()
                    .map(|arg| arg.def.arg.to_string())
                    .collect_vec(),
                body: function_def
                    .body
                    .into_iter()
                    .flat_map(Self::transpile)
                    .collect_vec(),
            }
            .pipe(once)
            .pipe(Either::Left),
            Stmt::AugAssign(aug_assign) => {
                Self::transpile_assign(vec![*aug_assign.target], aug_assign.value) // TODO make this actually aug assign
                    .pipe(Either::Left)
                    .pipe(Either::Right)
            }
            Stmt::AnnAssign(ann_assign) => {
                Self::transpile_assign(vec![*ann_assign.target], ann_assign.value.unwrap())
                    .pipe(Either::Left)
                    .pipe(Either::Right)
            }
            Stmt::Assign(assign) => Self::transpile_assign(assign.targets, assign.value)
                .pipe(Either::Left)
                .pipe(Either::Right),
            Stmt::For(r#for) => {
                let body = r#for
                    .body
                    .into_iter()
                    .flat_map(Self::transpile)
                    .collect_vec();
                if let Some(call) = r#for.iter.as_call_expr().filter(|call| {
                    call.func
                        .as_name_expr()
                        .is_some_and(|name| *name.id == *"range")
                }) {
                    let variable = r#for.target.expect_name_expr().id.to_string();
                    match &call.args[..] {
                        [end] => Self::ForNext {
                            variable,
                            from: "0".to_string(),
                            to: format!("<range arg {end:?}>"),
                            step: "1".to_string(),
                            body,
                        },
                        [start, end] => Self::ForNext {
                            variable,
                            from: format!("<range arg {start:?}>"),
                            to: format!("<range arg {end:?}>"),
                            step: "1".to_string(),
                            body,
                        },
                        [start, end, step] => Self::ForNext {
                            variable,
                            from: format!("<range arg {start:?}>"),
                            to: format!("<range arg {end:?}>"),
                            step: format!("<range arg {step:?}>"),
                            body,
                        },
                        _ => unreachable!("bad range: {:?}", call),
                    }
                    .pipe(once)
                    .pipe(Either::Left)
                } else if let Some(call) = r#for.iter.as_call_expr().filter(|call| {
                    call.func
                        .as_name_expr()
                        .is_some_and(|name| *name.id == *"enumerate")
                }) {
                    [Self::ForNext {
                        variable: "index".to_string(),
                        from: "0".to_string(),
                        to: format!(
                            "(LENGTH OF {})",
                            call.args
                                .iter()
                                .exactly_one()
                                .unwrap()
                                .as_name_expr()
                                .unwrap()
                                .id
                        ),
                        step: "1".to_string(),
                        body,
                    }]
                    .into_iter()
                    .pipe(Either::Right)
                } else {
                    let iter = r#for.iter.expect_name_expr().id;
                    [Self::ForNext {
                        variable: "index".to_string(),
                        from: "0".to_string(),
                        to: format!("(LENGTH OF {iter})"),
                        step: "1".to_string(),
                        body: once(Self::Assignment {
                            left: r#for.target.expect_name_expr().id.to_string(),
                            right: format!("{iter}[index]"),
                        })
                        .chain(body)
                        .collect_vec(),
                    }]
                    .into_iter()
                    .pipe(Either::Right)
                }
                .pipe(Either::Left)
                .pipe(Either::Right)
                .pipe(Either::Right)
            }
            Stmt::If(r#if) => Self::If {
                condition: expr_to_string(&r#if.test),
                body: r#if
                    .body
                    .into_iter()
                    .flat_map(Self::transpile)
                    .collect_vec(),
                else_body: r#if.orelse.is_empty().not().then(|| {
                    r#if.orelse
                        .into_iter()
                        .flat_map(Self::transpile)
                        .collect_vec()
                }),
            }
            .pipe(once)
            .pipe(Either::Left),
            Stmt::Expr(expr) => {
                if let Some(call) = expr.value.as_call_expr().filter(|call| {
                    call.func
                        .as_name_expr()
                        .is_some_and(|name| *name.id == *"print")
                }) {
                    Self::Display(call.args.iter().map(expr_to_string).join(", "))
                        .pipe(once)
                        .pipe(Either::Left)
                } else {
                    Self::Other(format!("<other statement {expr:?}>"))
                        .pipe(once)
                        .pipe(Either::Left)
                }
            }
            Stmt::Return(r#return) => Self::Return(r#return.value.as_deref().map(expr_to_string))
                .pipe(once)
                .pipe(Either::Left),
            Stmt::While(r#while) => Self::While {
                condition: expr_to_string(&r#while.test),
                body: r#while
                    .body
                    .into_iter()
                    .flat_map(Self::transpile)
                    .collect_vec(),
            }
            .pipe(once)
            .pipe(Either::Left),
            Stmt::Assert(_) => empty()
                .pipe(Either::<_, Empty<Self>>::Left)
                .pipe(Either::Right)
                .pipe(Either::Right)
                .pipe(Either::Right),
            _ => todo!("transpile statement:\n\n{statement:?}"),
        }
    }
}

fn expr_to_string(expr: &Expr<TextRange>) -> String {
    match expr {
        Expr::Name(name) => name.id.to_string(),
        Expr::Constant(constant) => match &constant.value {
            Constant::Bool(true) => "TRUE".to_string(),
            Constant::Bool(false) => "FALSE".to_string(),
            Constant::Str(string) => format!("\"{string}\""),
            Constant::Int(int) => format!("{int}"),
            Constant::Float(float) => format!("{float}"),
            Constant::Bytes(bytes) => format!("{bytes:?}"),
            Constant::None => "NULL".to_string(),
            Constant::Tuple(_) => unimplemented!(),
            Constant::Complex { .. } => unimplemented!(),
            Constant::Ellipsis => unimplemented!(),
        },
        Expr::Compare(compare) => {
            let left = expr_to_string(&compare.left);
            let right = expr_to_string(compare.comparators.iter().exactly_one().unwrap());
            let op = match compare.ops.iter().exactly_one().unwrap() {
                CmpOp::Lt => "<",
                CmpOp::LtE => "<=",
                CmpOp::Gt => ">",
                CmpOp::GtE => ">=",
                CmpOp::Is | CmpOp::Eq => "==",
                CmpOp::IsNot | CmpOp::NotEq => "!=",
                CmpOp::In => "IN",
                CmpOp::NotIn => "NOT IN",
            };
            format!("{left} {op} {right}")
        }
        Expr::BinOp(bin_op) => {
            let left = expr_to_string(&bin_op.left);
            let right = expr_to_string(&bin_op.right);
            let op = match bin_op.op {
                Operator::Add => "+",
                Operator::Sub => "-",
                Operator::Mult => "*",
                Operator::Div => "/",
                Operator::Mod => "%",
                Operator::Pow => "**",
                Operator::BitOr => "|",
                Operator::BitXor => "^",
                Operator::BitAnd => "&",
                Operator::FloorDiv => "//",
                _ => unimplemented!("{:?}", bin_op.op),
            };
            format!("{left} {op} {right}")
        }
        Expr::Call(call) => {
            if call
                .func
                .as_name_expr()
                .is_some_and(|name| *name.id == *"len")
            {
                let arg = call.args.iter().exactly_one().unwrap();
                format!("(LENGTH OF {})", expr_to_string(arg))
            } else {
                let func = call.func.as_name_expr().unwrap();
                format!(
                    "{}({})",
                    func.id,
                    call.args.iter().map(expr_to_string).join(", ")
                )
            }
        }
        Expr::Subscript(subscript) => {
            format!(
                "{}[{}]",
                expr_to_string(&subscript.value),
                expr_to_string(&subscript.slice)
            )
        }
        Expr::List(list) => {
            format!("[{}]", list.elts.iter().map(expr_to_string).join(", "))
        }
        Expr::BoolOp(bool_op) => {
            let op = match bool_op.op {
                BoolOp::And => "AND",
                BoolOp::Or => "OR",
            };
            let values = bool_op
                .values
                .iter()
                .map(expr_to_string)
                .join(&format!(" {op} "));
            format!("({values})")
        }
        Expr::UnaryOp(unary_op) => {
            let op = match unary_op.op {
                UnaryOp::Not => "NOT",
                UnaryOp::Invert => "~",
                UnaryOp::UAdd => "+",
                UnaryOp::USub => "-",
            };
            format!("{op} {}", expr_to_string(&unary_op.operand))
        }
        Expr::Tuple(tuple) => {
            format!("({})", tuple.elts.iter().map(expr_to_string).join(", "))
        }
        Expr::Slice(slice) => {
            let lower = slice
                .lower
                .as_deref()
                .map(expr_to_string)
                .unwrap_or_default();
            let upper = slice
                .upper
                .as_deref()
                .map(expr_to_string)
                .unwrap_or_default();
            let step = slice
                .step
                .as_deref()
                .map(expr_to_string)
                .map(|step| format!(":{step}"))
                .unwrap_or_default();
            format!("{lower}:{upper}{step}")
        }
        _ => format!("[[[ other expr: {expr:?} ]]]"),
    }
}

impl Display for Psuedocode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for statement in &self.statements {
            writeln!(
                f,
                "{}",
                DisplayStatement {
                    statement,
                    indent: 0
                }
            )?;
        }
        Ok(())
    }
}

struct DisplayStatement<'a> {
    statement: &'a Statement,
    indent: usize,
}

impl Display for DisplayStatement<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let indent = |f: &mut Formatter<'_>| {
            for _ in 0..self.indent {
                write!(f, "    ")?;
            }
            Ok(())
        };
        let write = |f: &mut Formatter<'_>, string| {
            indent(f)?;
            write!(f, "{string}")
        };
        let writeln = |f: &mut Formatter<'_>, string| {
            indent(f)?;
            writeln!(f, "{string}")
        };
        let writeln_statement = |f: &mut Formatter<'_>, statement| {
            writeln!(
                f,
                "{}",
                Self {
                    statement,
                    indent: self.indent + 1
                }
            )
        };
        match &self.statement {
            Statement::Comment { content } => write(f, format!("; {content}"))?,
            Statement::Process { name, args, body } => {
                writeln(
                    f,
                    format!(
                        "BEGIN {name}{}",
                        if args.is_empty() {
                            String::new()
                        } else {
                            format!("({})", args.join(", "))
                        }
                    ),
                )?;
                for statement in body {
                    writeln_statement(f, statement)?;
                }
                writeln(f, format!("END {name}"))?;
            }
            Statement::Input { out } => write(f, format!("INPUT {out}"))?,
            Statement::ForNext {
                variable,
                from,
                to,
                step,
                body,
            } => {
                writeln(f, format!("FOR {variable} = {from} TO {to} STEP {step}"))?;
                for statement in body {
                    writeln_statement(f, statement)?;
                }
                write(f, format!("NEXT {variable}"))?;
            }
            Statement::Assignment { left, right } => {
                write(f, format!("{left} = {right}"))?;
            }
            Statement::If {
                condition,
                body,
                else_body,
            } => {
                writeln(f, format!("IF {condition} THEN"))?;
                for statement in body {
                    writeln_statement(f, statement)?;
                }
                if let Some(else_body) = else_body {
                    writeln(f, "ELSE".to_string())?;
                    for statement in else_body {
                        writeln_statement(f, statement)?;
                    }
                }
                write(f, "ENDIF".to_string())?;
            }
            Statement::Return(value) => {
                if let Some(value) = value {
                    write(f, format!("RETURN {value}"))?;
                } else {
                    write(f, "RETURN".to_string())?;
                }
            }
            Statement::While { condition, body } => {
                writeln(f, format!("WHILE {condition}"))?;
                for statement in body {
                    writeln_statement(f, statement)?;
                }
                write(f, "ENDWHILE".to_string())?;
            }
            Statement::Display(expression) => {
                write(f, format!("DISPLAY {expression}"))?;
            }
            Statement::Other(other) => write!(f, "[[[ {other} ]]]")?,
        }
        Ok(())
    }
}

fn main() {}

fn transpile(python: &str) -> String {
    let tree = parse_tokens(lex(python, Mode::Module), Mode::Module, "<embedded>").unwrap();
    let pseudocode = Psuedocode {
        statements: tree
            .expect_module()
            .body
            .into_iter()
            .flat_map(Statement::transpile)
            .collect_vec(),
    };
    println!("{pseudocode}");
    todo!();
}

#[cfg(test)]
mod tests {
    use crate::transpile;

    #[test]
    fn works() {
        let actual = transpile(include_str!("input"));
        println!("\n{}", actual);
        let expected = include_str!("expected");
        assert_eq!(actual, expected);
    }
}

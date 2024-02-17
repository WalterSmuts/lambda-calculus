use std::fmt::Display;

use anyhow::{anyhow, Result};

pub mod parsing;

#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    Variable(Variable),
    Abstraction(Abstraction),
    Application(Application),
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Variable(variable) => variable.fmt(f),
            Term::Abstraction(abstraction) => abstraction.fmt(f),
            Term::Application(application) => application.fmt(f),
        }
    }
}

impl Term {
    pub fn reduce(&mut self) {
        while let Ok(()) = self.reduce_one_step() {}
    }

    fn reduce_one_step(&mut self) -> Result<()> {
        match self {
            Term::Variable(x) => Err(anyhow!("Cannot reduce a variable {x}")),
            Term::Abstraction(abstraction) => abstraction.body.reduce_one_step(),
            Term::Application(application) => {
                let t1 = &mut application.0;
                let t2 = &application.1;

                let x = match &**t1 {
                    Term::Abstraction(abstraction) => abstraction.substitute(t2),
                    _ => return t1.reduce_one_step(),
                };
                *self = x;
                Ok(())
            }
        }
    }

    // TODO: Remove clones...
    fn substitute_variables_with_arg(&mut self, variable: &Variable, arg: &Term) {
        match self {
            Term::Variable(x) => {
                if *x == *variable {
                    *self = arg.clone();
                }
            }
            Term::Abstraction(abstraction) => {
                let mut abstraction_clone = abstraction.clone();
                abstraction_clone
                    .body
                    .substitute_variables_with_arg(variable, arg);
                *self = Term::Abstraction(abstraction_clone);
            }
            Term::Application(application) => {
                let mut application_clone = application.clone();
                application_clone
                    .0
                    .substitute_variables_with_arg(variable, arg);
                application_clone
                    .1
                    .substitute_variables_with_arg(variable, arg);
                *self = Term::Application(application_clone);
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Variable {
    Lexical(char),
    Semantic(char, usize),
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Variable::Lexical(c) => c.fmt(f),
            Variable::Semantic(c, i) => write!(f, "{c}{i}"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Abstraction {
    arg: Variable,
    body: Box<Term>,
}
impl Abstraction {
    fn substitute(&self, second_term: &Term) -> Term {
        let mut new_body = self.body.clone();
        new_body.substitute_variables_with_arg(&self.arg, second_term);
        *new_body
    }
}

impl Display for Abstraction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "λ{}.{}", self.arg, self.body)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Application(Box<Term>, Box<Term>);

impl Display for Application {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let term_1 = match &*self.0 {
            Term::Abstraction(_) => format!("({})", self.0),
            Term::Application(Application(_, second_term_first_application)) => {
                if let Term::Abstraction(..) = **second_term_first_application {
                    format!("({})", self.0)
                } else {
                    format!("{}", self.0)
                }
            }
            _ => format!("{}", self.0),
        };
        let term_2 = if let Term::Application(_) = *self.1 {
            format!("({})", self.1)
        } else {
            format!("{}", self.1)
        };
        write!(f, "{} {}", term_1, term_2)
    }
}

impl From<u32> for Term {
    fn from(value: u32) -> Self {
        let mut body: Box<Term> = Box::new(Term::Variable(Variable::Lexical('z')));
        for _ in 0..value {
            body = Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable::Lexical('s'))),
                body,
            )))
        }
        Term::Abstraction(Abstraction {
            arg: Variable::Lexical('s'),
            body: Box::new(Term::Abstraction(Abstraction {
                arg: Variable::Lexical('z'),
                body,
            })),
        })
    }
}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn identity() {
        let identity = Term::Abstraction(Abstraction {
            arg: Variable::Lexical('x'),
            body: Box::new(Term::Variable(Variable::Lexical('x'))),
        });
        assert_eq!("λx.x", format!("{identity}"))
    }

    #[test]
    fn test_true() {
        let lambda_true = Term::Abstraction(Abstraction {
            arg: Variable::Lexical('x'),
            body: Box::new(Term::Abstraction(Abstraction {
                arg: Variable::Lexical('y'),
                body: Box::new(Term::Variable(Variable::Lexical('x'))),
            })),
        });
        assert_eq!("λx.λy.x", format!("{lambda_true}"))
    }

    #[test]
    fn test_false() {
        let lambda_false = Term::Abstraction(Abstraction {
            arg: Variable::Lexical('x'),
            body: Box::new(Term::Abstraction(Abstraction {
                arg: Variable::Lexical('y'),
                body: Box::new(Term::Variable(Variable::Lexical('y'))),
            })),
        });
        assert_eq!("λx.λy.y", format!("{lambda_false}"))
    }

    #[test]
    fn ambiguous_association() {
        // Application is left associative per default
        let left_associative = Term::Application(Application(
            Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable::Lexical('x'))),
                Box::new(Term::Variable(Variable::Lexical('y'))),
            ))),
            Box::new(Term::Variable(Variable::Lexical('z'))),
        ));

        // This one needs parenthesis to disambiguate
        let right_associative = Term::Application(Application(
            Box::new(Term::Variable(Variable::Lexical('x'))),
            Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable::Lexical('y'))),
                Box::new(Term::Variable(Variable::Lexical('z'))),
            ))),
        ));
        assert_ne!(
            format!("{left_associative}"),
            format!("{right_associative}")
        )
    }

    #[test]
    fn abstraction_association() {
        let term_1 = Term::Application(Application(
            Box::new(Term::Abstraction(Abstraction {
                arg: Variable::Lexical('x'),
                body: Box::new(Term::Variable(Variable::Lexical('y'))),
            })),
            Box::new(Term::Variable(Variable::Lexical('z'))),
        ));
        let term_2 = Term::Abstraction(Abstraction {
            arg: Variable::Lexical('x'),
            body: Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable::Lexical('y'))),
                Box::new(Term::Variable(Variable::Lexical('z'))),
            ))),
        });

        assert_ne!(format!("{term_1}"), format!("{term_2}"));
    }

    #[test]
    fn test_reduction_of_true() {
        use parsing::parse_term;
        let mut term = parse_term("(λx.λy.x) a b").unwrap();
        term.reduce();
        assert_eq!(term, parse_term("a").unwrap());
    }

    #[test]
    fn test_reduction_of_false() {
        use parsing::parse_term;
        let mut term = parse_term("(λx.λy.y) a b").unwrap();
        term.reduce();
        assert_eq!(term, parse_term("b").unwrap());
    }
}

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
pub struct Variable(char);

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
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
        // check if the second arg is also an application
        match self.1.as_ref() {
            Term::Application(_) => write!(f, "{} ({})", self.0, self.1),
            _ => write!(f, "{} {}", self.0, self.1),
        }
    }
}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn identity() {
        let identity = Term::Abstraction(Abstraction {
            arg: Variable('x'),
            body: Box::new(Term::Variable(Variable('x'))),
        });
        assert_eq!("λx.x", format!("{identity}"))
    }

    #[test]
    fn test_true() {
        let lambda_true = Term::Abstraction(Abstraction {
            arg: Variable('x'),
            body: Box::new(Term::Abstraction(Abstraction {
                arg: Variable('y'),
                body: Box::new(Term::Variable(Variable('x'))),
            })),
        });
        assert_eq!("λx.λy.x", format!("{lambda_true}"))
    }

    #[test]
    fn test_false() {
        let lambda_false = Term::Abstraction(Abstraction {
            arg: Variable('x'),
            body: Box::new(Term::Abstraction(Abstraction {
                arg: Variable('y'),
                body: Box::new(Term::Variable(Variable('y'))),
            })),
        });
        assert_eq!("λx.λy.y", format!("{lambda_false}"))
    }

    #[test]
    fn ambiguous_association() {
        // Application is left associative per default
        let left_associative = Term::Application(Application(
            Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable('x'))),
                Box::new(Term::Variable(Variable('y'))),
            ))),
            Box::new(Term::Variable(Variable('z'))),
        ));

        // This one needs parenthesis to disambiguate
        let right_associative = Term::Application(Application(
            Box::new(Term::Variable(Variable('x'))),
            Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable('y'))),
                Box::new(Term::Variable(Variable('z'))),
            ))),
        ));
        assert_ne!(
            format!("{left_associative}"),
            format!("{right_associative}")
        )
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

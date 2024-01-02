use std::fmt::Display;

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

pub struct Variable(char);

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

pub struct Abstraction {
    arg: Variable,
    body: Box<Term>,
}

impl Display for Abstraction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "λ{}.{}", self.arg, self.body)
    }
}

pub struct Application(Box<Term>, Box<Term>);

impl Display for Application {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.0, self.1)
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
        let left_associative = Term::Application(Application(
            Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable('x'))),
                Box::new(Term::Variable(Variable('y'))),
            ))),
            Box::new(Term::Variable(Variable('z'))),
        ));
        let right_associative = Term::Application(Application(
            Box::new(Term::Variable(Variable('x'))),
            Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable('y'))),
                Box::new(Term::Variable(Variable('z'))),
            ))),
        ));
        assert_eq!(
            format!("{left_associative}"),
            format!("{right_associative}")
        )
    }
}

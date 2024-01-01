pub enum Term {
    Variable(Variable),
    Abstraction(Abstraction),
    Application(Application),
}

pub struct Variable(char);

pub struct Abstraction {
    #[allow(dead_code)]
    arg: Variable,
    #[allow(dead_code)]
    body: Box<Term>,
}

pub struct Application(Box<Term>, Box<Term>);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn identity() {
        let _identity = Term::Abstraction(Abstraction {
            arg: Variable('x'),
            body: Box::new(Term::Variable(Variable('x'))),
        });
    }

    #[test]
    fn test_true() {
        let _lambda_true = Term::Abstraction(Abstraction {
            arg: Variable('x'),
            body: Box::new(Term::Abstraction(Abstraction {
                arg: Variable('y'),
                body: Box::new(Term::Variable(Variable('x'))),
            })),
        });
    }

    #[test]
    fn test_false() {
        let _lambda_false = Term::Abstraction(Abstraction {
            arg: Variable('x'),
            body: Box::new(Term::Abstraction(Abstraction {
                arg: Variable('y'),
                body: Box::new(Term::Variable(Variable('y'))),
            })),
        });
    }
}

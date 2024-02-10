use nom::branch::alt;
use nom::character::complete::anychar;
use nom::character::complete::char;
use nom::combinator::all_consuming;
use nom::combinator::map;
use nom::error::Error;
use nom::sequence::preceded;
use nom::sequence::separated_pair;
use nom::sequence::tuple;
use nom::IResult;
use std::fmt::Display;

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

#[derive(Debug, PartialEq, Clone)]
pub struct Variable(char);

fn parse_variable(input: &str) -> IResult<&str, Variable> {
    let (remaining_input, parsed_char) = anychar(input)?;
    match parsed_char {
        '(' | ')' | 'λ' | '.' => {
            return Err(nom::Err::Error(Error::new(
                "{parsed_char} can't be a variable name.",
                nom::error::ErrorKind::Tag,
            )));
        }
        _ => (),
    };
    let variable = Variable(parsed_char);

    Ok((remaining_input, variable))
}

fn parse_abstraction(input: &str) -> IResult<&str, Abstraction> {
    preceded(
        char('λ'),
        map(
            tuple((
                parse_variable,
                preceded(char('.'), parse_term_non_consuming),
            )),
            |(arg, body)| Abstraction {
                arg,
                body: Box::new(body),
            },
        ),
    )(input)
}

fn parse_application(input: &str) -> IResult<&str, Application> {
    map(
        separated_pair(
            parse_term_non_consuming,
            char(' '),
            parse_term_non_consuming,
        ),
        |(term1, term2)| -> Application { Application(Box::new(term1), Box::new(term2)) },
    )(input)
}

fn parse_term_non_consuming(input: &str) -> IResult<&str, Term> {
    alt((
        map(parse_variable, Term::Variable),
        map(parse_application, Term::Application),
        map(parse_abstraction, Term::Abstraction),
    ))(input)
}

pub fn parse_term(input: &str) -> IResult<&str, Term> {
    alt((
        map(all_consuming(parse_variable), Term::Variable),
        map(all_consuming(parse_application), Term::Application),
        map(all_consuming(parse_abstraction), Term::Abstraction),
    ))(input)
}

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
    fn test_parse_variable() {
        let (_, x) = parse_term("x").unwrap();
        assert_eq!(x, Term::Variable(Variable('x')));
    }

    #[test]
    fn test_parse_abstraction() {
        let (_, term) = parse_term("λx.x").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable('x'),
                body: Box::new(Term::Variable(Variable('x'))),
            })
        );
    }

    #[test]
    fn test_parse_application() {
        let (_, term) = parse_term("x y").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Variable(Variable('x'))),
                Box::new(Term::Variable(Variable('y'))),
            ))
        );
    }

    #[test]
    fn parsing_preserves_application_left_associativity() {
        let (_, term) = parse_term("a b c").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Application(Application(
                    Box::new(Term::Variable(Variable('a'))),
                    Box::new(Term::Variable(Variable('b'))),
                ))),
                Box::new(Term::Variable(Variable('c'))),
            ))
        );
    }
}

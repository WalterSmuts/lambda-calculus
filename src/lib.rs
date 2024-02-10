use nom::branch::alt;
use nom::character::complete::anychar;
use nom::character::complete::char;
use nom::combinator::all_consuming;
use nom::combinator::map;
use nom::error::Error;
use nom::multi::fold_many1;
use nom::sequence::preceded;
use nom::sequence::terminated;
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
    let (rest, term) = parse_term_non_consuming_non_application(input)?;
    let (rest, term) = fold_many1(
        preceded(char(' '), parse_term_non_consuming_non_application),
        move || term.clone(),
        |left_term, right_term| {
            Term::Application(Application(Box::new(left_term), Box::new(right_term)))
        },
    )(rest)?;
    match term {
        Term::Application(term) => Ok((rest, term)),
        _ => unreachable!("{term}"),
    }
}

fn parse_term_non_consuming_non_application(input: &str) -> IResult<&str, Term> {
    alt((
        terminated(preceded(char('('), parse_term_non_consuming), char(')')),
        map(parse_variable, Term::Variable),
        map(parse_abstraction, Term::Abstraction),
    ))(input)
}

fn parse_term_non_consuming(input: &str) -> IResult<&str, Term> {
    alt((
        map(parse_application, Term::Application),
        parse_term_non_consuming_non_application,
    ))(input)
}

pub fn parse_term(input: &str) -> IResult<&str, Term> {
    alt((
        map(all_consuming(parse_application), Term::Application),
        map(all_consuming(parse_variable), Term::Variable),
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

    #[test]
    fn parse_complex_term() {
        let (_, term) = parse_term("λx.λy.λz.a b c").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable('x'),
                body: Box::new(Term::Abstraction(Abstraction {
                    arg: Variable('y'),
                    body: Box::new(Term::Abstraction(Abstraction {
                        arg: Variable('z'),
                        body: Box::new(Term::Application(Application(
                            Box::new(Term::Application(Application(
                                Box::new(Term::Variable(Variable('a'))),
                                Box::new(Term::Variable(Variable('b'))),
                            ))),
                            Box::new(Term::Variable(Variable('c'))),
                        ))),
                    })),
                })),
            })
        );
    }

    #[test]
    fn parenthesis_around_application_left_associative() {
        let (_, term) = parse_term("(a b) c").unwrap();
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

    #[test]
    fn parenthesis_around_application_right_associative() {
        let (_, term) = parse_term("a (b c)").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Variable(Variable('a'))),
                Box::new(Term::Application(Application(
                    Box::new(Term::Variable(Variable('b'))),
                    Box::new(Term::Variable(Variable('c'))),
                ))),
            ))
        );
    }

    #[test]
    fn brackets_around_variable() {
        let (_, term) = parse_term("(a) b").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Variable(Variable('a'))),
                Box::new(Term::Variable(Variable('b'))),
            ))
        );
    }

    #[test]
    fn brackets_around_abstraction() {
        let (_, term) = parse_term("λx.(λy.x)").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable('x'),
                body: Box::new(Term::Abstraction(Abstraction {
                    arg: Variable('y'),
                    body: Box::new(Term::Variable(Variable('x'))),
                })),
            })
        );
    }

    #[test]
    fn parse_abstraction_before_application() {
        let (_, term) = parse_term("λy.(a b) c").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable('y'),
                body: Box::new(Term::Application(Application(
                    Box::new(Term::Application(Application(
                        Box::new(Term::Variable(Variable('a'))),
                        Box::new(Term::Variable(Variable('b'))),
                    ))),
                    Box::new(Term::Variable(Variable('c'))),
                ))),
            })
        );
    }

    #[test]
    fn test_parse_term_non_consuming() {
        let (_, term) = parse_term_non_consuming("(a b) c").unwrap();
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

    #[test]
    fn parse_more_complex_term() {
        let (_, term) = parse_term("λx.λy.(a b) (λz.λw.(c d e) f)").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable('x'),
                body: Box::new(Term::Abstraction(Abstraction {
                    arg: Variable('y'),
                    body: Box::new(Term::Application(Application(
                        Box::new(Term::Application(Application(
                            Box::new(Term::Variable(Variable('a'))),
                            Box::new(Term::Variable(Variable('b'))),
                        ))),
                        Box::new(Term::Abstraction(Abstraction {
                            arg: Variable('z'),
                            body: Box::new(Term::Abstraction(Abstraction {
                                arg: Variable('w'),
                                body: Box::new(Term::Application(Application(
                                    Box::new(Term::Application(Application(
                                        Box::new(Term::Application(Application(
                                            Box::new(Term::Variable(Variable('c'))),
                                            Box::new(Term::Variable(Variable('d'))),
                                        ))),
                                        Box::new(Term::Variable(Variable('e'))),
                                    ))),
                                    Box::new(Term::Variable(Variable('f'))),
                                ))),
                            })),
                        })),
                    ))),
                })),
            })
        );
    }

    #[test]
    fn test_round_trip() {
        let term = Term::Abstraction(Abstraction {
            arg: Variable('x'),
            body: Box::new(Term::Abstraction(Abstraction {
                arg: Variable('y'),
                body: Box::new(Term::Application(Application(
                    Box::new(Term::Application(Application(
                        Box::new(Term::Variable(Variable('a'))),
                        Box::new(Term::Variable(Variable('b'))),
                    ))),
                    Box::new(Term::Abstraction(Abstraction {
                        arg: Variable('z'),
                        body: Box::new(Term::Abstraction(Abstraction {
                            arg: Variable('w'),
                            body: Box::new(Term::Application(Application(
                                Box::new(Term::Application(Application(
                                    Box::new(Term::Application(Application(
                                        Box::new(Term::Variable(Variable('c'))),
                                        Box::new(Term::Variable(Variable('d'))),
                                    ))),
                                    Box::new(Term::Variable(Variable('e'))),
                                ))),
                                Box::new(Term::Variable(Variable('f'))),
                            ))),
                        })),
                    })),
                ))),
            })),
        });
        let serialised_term = format!("{term}");
        let (_, parsed_term) = parse_term(&serialised_term).unwrap();
        assert_eq!(term, parsed_term);
    }
}

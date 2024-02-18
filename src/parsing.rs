use super::*;
use anyhow::Result;
use nom::branch::alt;
use nom::character::complete::anychar;
use nom::character::complete::char;
use nom::character::complete::digit1;
use nom::combinator::all_consuming;
use nom::combinator::map;
use nom::error::Error;
use nom::multi::fold_many1;
use nom::sequence::preceded;
use nom::sequence::terminated;
use nom::sequence::tuple;
use nom::IResult;

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
    let variable = Variable::Lexical(parsed_char);

    Ok((remaining_input, variable))
}

fn parse_abstraction_inner(input: &str) -> IResult<&str, Abstraction> {
    map(
        tuple((
            parse_variable,
            alt((
                preceded(char('.'), parse_term_non_consuming),
                map(parse_abstraction_inner, Term::Abstraction),
            )),
        )),
        |(arg, body)| Abstraction {
            arg,
            body: Box::new(body),
        },
    )(input)
}

fn parse_abstraction(input: &str) -> IResult<&str, Abstraction> {
    preceded(char('λ'), parse_abstraction_inner)(input)
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

fn parse_nat(input: &str) -> IResult<&str, Term> {
    map(digit1, |nat: &str| nat.parse::<u32>().unwrap().into())(input)
}

fn parse_term_non_consuming_non_application(input: &str) -> IResult<&str, Term> {
    alt((
        terminated(preceded(char('('), parse_term_non_consuming), char(')')),
        parse_nat,
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

pub fn parse_term(input: &str) -> Result<Term> {
    alt((
        map(all_consuming(parse_application), Term::Application),
        all_consuming(parse_nat),
        map(all_consuming(parse_variable), Term::Variable),
        map(all_consuming(parse_abstraction), Term::Abstraction),
    ))(input)
    .map(|(_rest, result)| result)
    .map_err(|err| anyhow::anyhow!("{err}"))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_variable() {
        let x = parse_term("x").unwrap();
        assert_eq!(x, Term::Variable(Variable::Lexical('x')));
    }

    #[test]
    fn test_parse_abstraction() {
        let term = parse_term("λx.x").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable::Lexical('x'),
                body: Box::new(Term::Variable(Variable::Lexical('x'))),
            })
        );
    }

    #[test]
    fn test_parse_application() {
        let term = parse_term("x y").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Variable(Variable::Lexical('x'))),
                Box::new(Term::Variable(Variable::Lexical('y'))),
            ))
        );
    }

    #[test]
    fn parsing_preserves_application_left_associativity() {
        let term = parse_term("a b c").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Application(Application(
                    Box::new(Term::Variable(Variable::Lexical('a'))),
                    Box::new(Term::Variable(Variable::Lexical('b'))),
                ))),
                Box::new(Term::Variable(Variable::Lexical('c'))),
            ))
        );
    }

    #[test]
    fn parse_complex_term() {
        let term = parse_term("λx.λy.λz.a b c").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable::Lexical('x'),
                body: Box::new(Term::Abstraction(Abstraction {
                    arg: Variable::Lexical('y'),
                    body: Box::new(Term::Abstraction(Abstraction {
                        arg: Variable::Lexical('z'),
                        body: Box::new(Term::Application(Application(
                            Box::new(Term::Application(Application(
                                Box::new(Term::Variable(Variable::Lexical('a'))),
                                Box::new(Term::Variable(Variable::Lexical('b'))),
                            ))),
                            Box::new(Term::Variable(Variable::Lexical('c'))),
                        ))),
                    })),
                })),
            })
        );
    }

    #[test]
    fn parenthesis_around_application_left_associative() {
        let term = parse_term("(a b) c").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Application(Application(
                    Box::new(Term::Variable(Variable::Lexical('a'))),
                    Box::new(Term::Variable(Variable::Lexical('b'))),
                ))),
                Box::new(Term::Variable(Variable::Lexical('c'))),
            ))
        );
    }

    #[test]
    fn parenthesis_around_application_right_associative() {
        let term = parse_term("a (b c)").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Variable(Variable::Lexical('a'))),
                Box::new(Term::Application(Application(
                    Box::new(Term::Variable(Variable::Lexical('b'))),
                    Box::new(Term::Variable(Variable::Lexical('c'))),
                ))),
            ))
        );
    }

    #[test]
    fn brackets_around_variable() {
        let term = parse_term("(a) b").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Variable(Variable::Lexical('a'))),
                Box::new(Term::Variable(Variable::Lexical('b'))),
            ))
        );
    }

    #[test]
    fn brackets_around_abstraction() {
        let term = parse_term("λx.(λy.x)").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable::Lexical('x'),
                body: Box::new(Term::Abstraction(Abstraction {
                    arg: Variable::Lexical('y'),
                    body: Box::new(Term::Variable(Variable::Lexical('x'))),
                })),
            })
        );
    }

    #[test]
    fn parse_abstraction_before_application() {
        let term = parse_term("λy.(a b) c").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable::Lexical('y'),
                body: Box::new(Term::Application(Application(
                    Box::new(Term::Application(Application(
                        Box::new(Term::Variable(Variable::Lexical('a'))),
                        Box::new(Term::Variable(Variable::Lexical('b'))),
                    ))),
                    Box::new(Term::Variable(Variable::Lexical('c'))),
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
                    Box::new(Term::Variable(Variable::Lexical('a'))),
                    Box::new(Term::Variable(Variable::Lexical('b'))),
                ))),
                Box::new(Term::Variable(Variable::Lexical('c'))),
            ))
        );
    }

    #[test]
    fn parse_more_complex_term() {
        let term = parse_term("λx.λy.(a b) (λz.λw.(c d e) f)").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction {
                arg: Variable::Lexical('x'),
                body: Box::new(Term::Abstraction(Abstraction {
                    arg: Variable::Lexical('y'),
                    body: Box::new(Term::Application(Application(
                        Box::new(Term::Application(Application(
                            Box::new(Term::Variable(Variable::Lexical('a'))),
                            Box::new(Term::Variable(Variable::Lexical('b'))),
                        ))),
                        Box::new(Term::Abstraction(Abstraction {
                            arg: Variable::Lexical('z'),
                            body: Box::new(Term::Abstraction(Abstraction {
                                arg: Variable::Lexical('w'),
                                body: Box::new(Term::Application(Application(
                                    Box::new(Term::Application(Application(
                                        Box::new(Term::Application(Application(
                                            Box::new(Term::Variable(Variable::Lexical('c'))),
                                            Box::new(Term::Variable(Variable::Lexical('d'))),
                                        ))),
                                        Box::new(Term::Variable(Variable::Lexical('e'))),
                                    ))),
                                    Box::new(Term::Variable(Variable::Lexical('f'))),
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
            arg: Variable::Lexical('x'),
            body: Box::new(Term::Abstraction(Abstraction {
                arg: Variable::Lexical('y'),
                body: Box::new(Term::Application(Application(
                    Box::new(Term::Application(Application(
                        Box::new(Term::Variable(Variable::Lexical('a'))),
                        Box::new(Term::Variable(Variable::Lexical('b'))),
                    ))),
                    Box::new(Term::Abstraction(Abstraction {
                        arg: Variable::Lexical('z'),
                        body: Box::new(Term::Abstraction(Abstraction {
                            arg: Variable::Lexical('w'),
                            body: Box::new(Term::Application(Application(
                                Box::new(Term::Application(Application(
                                    Box::new(Term::Application(Application(
                                        Box::new(Term::Variable(Variable::Lexical('c'))),
                                        Box::new(Term::Variable(Variable::Lexical('d'))),
                                    ))),
                                    Box::new(Term::Variable(Variable::Lexical('e'))),
                                ))),
                                Box::new(Term::Variable(Variable::Lexical('f'))),
                            ))),
                        })),
                    })),
                ))),
            })),
        });
        let serialised_term = format!("{term}");
        let parsed_term = parse_term(&serialised_term).unwrap();
        assert_eq!(term, parsed_term);
    }

    #[test]
    fn parse_nat_0() {
        let term = parse_term("0").unwrap();
        assert_eq!(term, parse_term("λs.λz.z").unwrap());
    }

    #[test]
    fn parse_nat_1() {
        let term = parse_term("1").unwrap();
        assert_eq!(term, parse_term("λs.λz.s z").unwrap());
    }

    #[test]
    fn parse_nat_2() {
        let term = parse_term("2").unwrap();
        assert_eq!(term, parse_term("λs.λz.s (s z)").unwrap());
    }

    #[test]
    fn parse_complex_nat() {
        let term = parse_term("λa.1 2").unwrap();
        assert_eq!(term, parse_term("λa.(λs.λz.s z) (λs.λz.s (s z))").unwrap());
    }

    #[test]
    fn parse_compact_abstraction() {
        let term = parse_term("λx.λy.x").unwrap();
        let compact_term = parse_term("λxy.x").unwrap();
        assert_eq!(term, compact_term);
    }
}

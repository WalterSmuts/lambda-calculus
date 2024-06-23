use super::*;
use anyhow::Result;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::anychar;
use nom::character::complete::char;
use nom::character::complete::digit1;
use nom::combinator::all_consuming;
use nom::combinator::map;
use nom::error::Error;
use nom::multi::fold_many1;
use nom::multi::many0;
use nom::sequence::preceded;
use nom::sequence::terminated;
use nom::sequence::tuple;
use nom::IResult;

#[derive(PartialEq, Debug)]
struct LetBinding {
    var: Variable,
    term: Term,
}

fn parse_type(input: &str) -> IResult<&str, LambdaType> {
    alt((
        map(tag("Boolean"), |_| LambdaType::Boolean),
        map(tag("Integer"), |_| LambdaType::Integer),
    ))(input)
}

fn parse_typed_variable(input: &str) -> IResult<&str, Variable> {
    map(
        tuple((parse_untyped_variable, preceded(char(':'), parse_type))),
        |(var, lambda_type)| {
            let mut var = var.clone();
            var.set_type(lambda_type);
            var
        },
    )(input)
}

fn parse_untyped_variable(input: &str) -> IResult<&str, Variable> {
    let (remaining_input, parsed_char) = anychar(input)?;
    match parsed_char {
        '(' | ')' | 'λ' | '.' | '=' | '\n' => {
            return Err(nom::Err::Error(Error::new(
                "{parsed_char} can't be a variable name.",
                nom::error::ErrorKind::Tag,
            )));
        }
        _ => (),
    };
    let variable = Variable::new(parsed_char);

    Ok((remaining_input, variable))
}

fn parse_variable(input: &str) -> IResult<&str, Variable> {
    alt((parse_typed_variable, parse_untyped_variable))(input)
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
        |(arg, body)| Abstraction::new(arg, body),
    )(input)
}

fn parse_abstraction(input: &str) -> IResult<&str, Abstraction> {
    preceded(char('λ'), parse_abstraction_inner)(input)
}

fn parse_application(input: &str) -> IResult<&str, Application> {
    let (rest, term) = parse_term_non_consuming_non_application(input)?;
    let (rest, term) = fold_many1(
        preceded(many0(char(' ')), parse_term_non_consuming_non_application),
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

fn parse_let_binding(input: &str) -> IResult<&str, LetBinding> {
    let (input, var) = preceded(tag("let "), parse_variable)(input)?;
    let (input, _) = tag(" = ")(input)?;
    let (input, term) = alt((
        map(parse_application, Term::Application),
        parse_nat,
        map(parse_variable, Term::Variable),
        map(parse_abstraction, Term::Abstraction),
    ))(input)?;
    let (input, _) = char('\n')(input)?;
    Ok((input, LetBinding { var, term }))
}

pub fn parse_term(input: &str) -> Result<Term> {
    let (input, mut let_bindings) = many0(parse_let_binding)(input).unwrap();

    let mut term = alt((
        map(all_consuming(parse_application), Term::Application),
        all_consuming(parse_nat),
        map(all_consuming(parse_variable), Term::Variable),
        map(all_consuming(parse_abstraction), Term::Abstraction),
    ))(input)
    .map(|(_rest, result)| result)
    .map_err(|err| anyhow::anyhow!("{err}"))?;

    while let Some(let_binding) = let_bindings.pop() {
        term = Term::Application(Application(
            Box::new(Term::Abstraction(Abstraction::new(let_binding.var, term))),
            Box::new(let_binding.term),
        ))
    }
    Ok(term)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_variable() {
        let x = parse_term("x").unwrap();
        assert_eq!(x, Term::Variable(Variable::new('x')));
    }

    #[test]
    fn test_parse_abstraction() {
        let term = parse_term("λx.x").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction::new(
                Variable::new('x'),
                Term::Variable(Variable::new('x')),
            ))
        );
    }

    #[test]
    fn test_parse_application() {
        let term = parse_term("x y").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Variable(Variable::new('x'))),
                Box::new(Term::Variable(Variable::new('y'))),
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
                    Box::new(Term::Variable(Variable::new('a'))),
                    Box::new(Term::Variable(Variable::new('b'))),
                ))),
                Box::new(Term::Variable(Variable::new('c'))),
            ))
        );
    }

    #[test]
    fn parse_complex_term() {
        let term = parse_term("λx.λy.λz.a b c").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction::new(
                Variable::new('x'),
                Term::Abstraction(Abstraction::new(
                    Variable::new('y'),
                    Term::Abstraction(Abstraction::new(
                        Variable::new('z'),
                        Term::Application(Application(
                            Box::new(Term::Application(Application(
                                Box::new(Term::Variable(Variable::new('a'))),
                                Box::new(Term::Variable(Variable::new('b'))),
                            ))),
                            Box::new(Term::Variable(Variable::new('c'))),
                        )),
                    )),
                ))
            ),)
        );
    }

    #[test]
    fn parenthesis_around_application_left_associative() {
        let term = parse_term("(a b) c").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Application(Application(
                    Box::new(Term::Variable(Variable::new('a'))),
                    Box::new(Term::Variable(Variable::new('b'))),
                ))),
                Box::new(Term::Variable(Variable::new('c'))),
            ))
        );
    }

    #[test]
    fn parenthesis_around_application_right_associative() {
        let term = parse_term("a (b c)").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Variable(Variable::new('a'))),
                Box::new(Term::Application(Application(
                    Box::new(Term::Variable(Variable::new('b'))),
                    Box::new(Term::Variable(Variable::new('c'))),
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
                Box::new(Term::Variable(Variable::new('a'))),
                Box::new(Term::Variable(Variable::new('b'))),
            ))
        );
    }

    #[test]
    fn brackets_around_abstraction() {
        let term = parse_term("λx.(λy.x)").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction::new(
                Variable::new('x'),
                Term::Abstraction(Abstraction::new(
                    Variable::new('y'),
                    Term::Variable(Variable::new('x')),
                )),
            ))
        );
    }

    #[test]
    fn parse_abstraction_before_application() {
        let term = parse_term("λy.(a b) c").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction::new(
                Variable::new('y'),
                Term::Application(Application(
                    Box::new(Term::Application(Application(
                        Box::new(Term::Variable(Variable::new('a'))),
                        Box::new(Term::Variable(Variable::new('b'))),
                    ))),
                    Box::new(Term::Variable(Variable::new('c'))),
                )),
            ))
        );
    }

    #[test]
    fn test_parse_term_non_consuming() {
        let (_, term) = parse_term_non_consuming("(a b) c").unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Application(Application(
                    Box::new(Term::Variable(Variable::new('a'))),
                    Box::new(Term::Variable(Variable::new('b'))),
                ))),
                Box::new(Term::Variable(Variable::new('c'))),
            ))
        );
    }

    #[test]
    fn parse_more_complex_term() {
        let term = parse_term("λx.λy.(a b) (λz.λw.(c d e) f)").unwrap();
        assert_eq!(
            term,
            Term::Abstraction(Abstraction::new(
                Variable::new('x'),
                Term::Abstraction(Abstraction::new(
                    Variable::new('y'),
                    Term::Application(Application(
                        Box::new(Term::Application(Application(
                            Box::new(Term::Variable(Variable::new('a'))),
                            Box::new(Term::Variable(Variable::new('b'))),
                        ))),
                        Box::new(Term::Abstraction(Abstraction::new(
                            Variable::new('z'),
                            Term::Abstraction(Abstraction::new(
                                Variable::new('w'),
                                Term::Application(Application(
                                    Box::new(Term::Application(Application(
                                        Box::new(Term::Application(Application(
                                            Box::new(Term::Variable(Variable::new('c'))),
                                            Box::new(Term::Variable(Variable::new('d'))),
                                        ))),
                                        Box::new(Term::Variable(Variable::new('e'))),
                                    ))),
                                    Box::new(Term::Variable(Variable::new('f'))),
                                )),
                            )),
                        ))),
                    )),
                ))
            ),)
        );
    }

    #[test]
    fn test_round_trip() {
        let term = Term::Abstraction(Abstraction::new(
            Variable::new('x'),
            Term::Abstraction(Abstraction::new(
                Variable::new('y'),
                Term::Application(Application(
                    Box::new(Term::Application(Application(
                        Box::new(Term::Variable(Variable::new('a'))),
                        Box::new(Term::Variable(Variable::new('b'))),
                    ))),
                    Box::new(Term::Abstraction(Abstraction::new(
                        Variable::new('z'),
                        Term::Abstraction(Abstraction::new(
                            Variable::new('w'),
                            Term::Application(Application(
                                Box::new(Term::Application(Application(
                                    Box::new(Term::Application(Application(
                                        Box::new(Term::Variable(Variable::new('c'))),
                                        Box::new(Term::Variable(Variable::new('d'))),
                                    ))),
                                    Box::new(Term::Variable(Variable::new('e'))),
                                ))),
                                Box::new(Term::Variable(Variable::new('f'))),
                            )),
                        )),
                    ))),
                )),
            )),
        ));
        let serialised_term = format!("{term}");
        let parsed_term = parse_term(&serialised_term).unwrap();
        assert_eq!(term, parsed_term);
    }

    #[test]
    fn parse_nat_0() {
        let mut term = parse_term("0").unwrap();
        term.erase_types();
        assert_eq!(term, parse_term("λs.λz.z").unwrap());
    }

    #[test]
    fn parse_nat_1() {
        let mut term = parse_term("1").unwrap();
        term.erase_types();
        assert_eq!(term, parse_term("λs.λz.s z").unwrap());
    }

    #[test]
    fn parse_nat_2() {
        let mut term = parse_term("2").unwrap();
        term.erase_types();
        assert_eq!(term, parse_term("λs.λz.s (s z)").unwrap());
    }

    #[test]
    fn parse_complex_nat() {
        let mut term = parse_term("λa.1 2").unwrap();
        term.erase_types();
        assert_eq!(term, parse_term("λa.(λs.λz.s z) (λs.λz.s (s z))").unwrap());
    }

    #[test]
    fn parse_compact_abstraction() {
        let term = parse_term("λx.λy.x").unwrap();
        let compact_term = parse_term("λxy.x").unwrap();
        assert_eq!(term, compact_term);
    }

    #[test]
    fn parse_compact_application() {
        let term = parse_term("abc").unwrap();
        let compact_term = parse_term("a b c").unwrap();
        assert_eq!(term, compact_term);
    }

    #[test]
    fn single_let_binding() {
        let (rest, let_binding) = parse_let_binding("let x = y\n").unwrap();
        assert_eq!(rest, "");
        assert_eq!(
            let_binding,
            LetBinding {
                var: Variable::new('x'),
                term: Term::Variable(Variable::new('y'))
            }
        )
    }

    #[test]
    fn single_let_term() {
        use indoc::indoc;
        let term = parse_term(indoc! {"
        let x = y
        x"
        })
        .unwrap();
        assert_eq!(
            term,
            Term::Application(Application(
                Box::new(Term::Abstraction(Abstraction::new(
                    Variable::new('x'),
                    Term::Variable(Variable::new('x')),
                ))),
                Box::new(Term::Variable(Variable::new('y')))
            ))
        )
    }

    #[test]
    fn let_bindings() {
        use indoc::indoc;
        let mut term = parse_term(indoc! {"
        let x = 1
        let y = 2
        let p = λm.λn.λf.λx.m f (n f x)
        p x y"
        })
        .unwrap();
        term.reduce();
        let result: u32 = term.try_into().unwrap();
        assert_eq!(result, 3)
    }

    #[test]
    fn parse_typed_abstraction() {
        let mut typed_integer_abstraction = parse_term("λx:Boolean.x").unwrap();
        let untyped_integer_abstraction = parse_term("λx.x").unwrap();
        let mut typed_boolean_abstraction = parse_term("λx:Integer.x").unwrap();
        let untyped_boolean_abstraction = parse_term("λx.x").unwrap();
        typed_integer_abstraction.erase_types();
        typed_boolean_abstraction.erase_types();
        assert_eq!(typed_integer_abstraction, untyped_integer_abstraction);
        assert_eq!(typed_boolean_abstraction, untyped_boolean_abstraction);
    }
}

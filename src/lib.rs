use std::fmt::Display;
use std::sync::atomic::AtomicUsize;

use anyhow::anyhow;
use anyhow::Result;

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
    fn alpha_convert(&mut self) {
        static COUNT: AtomicUsize = AtomicUsize::new(0);
        match self {
            Term::Variable(_) => (),
            Term::Abstraction(abstraction) => {
                let Variable { inner: c, .. } = abstraction.arg;
                {
                    abstraction.body.alpha_convert();
                    let mut new_variable = Variable::new(c);
                    new_variable
                        .set_identifier(COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
                    abstraction.body.substitute_variables_with_arg(
                        &abstraction.arg,
                        &Term::Variable(new_variable.clone()),
                    );
                    abstraction.arg = new_variable;
                }
            }
            Term::Application(application) => {
                application.0.alpha_convert();
                application.1.alpha_convert();
            }
        }
    }

    fn erase_types(&mut self) {
        match self {
            Term::Variable(variable) => variable.erase_types(),
            Term::Abstraction(abstraction) => {
                abstraction.lambda_type = None;
                abstraction.body.erase_types();
                abstraction.arg.erase_types();
            }
            Term::Application(application) => {
                application.0.erase_types();
                application.1.erase_types();
            }
        }
    }

    pub fn reduce(&mut self) {
        self.erase_types();
        self.alpha_convert();
        while let Ok(()) = self.reduce_one_step() {
            self.alpha_convert();
        }
    }

    fn reduce_one_step(&mut self) -> Result<()> {
        match self {
            Term::Variable(x) => Err(anyhow!("Cannot reduce a variable {x}")),
            Term::Abstraction(abstraction) => abstraction.body.reduce_one_step(),
            Term::Application(application) => {
                let t1 = &mut application.0;
                let t2 = &mut application.1;

                let x = match &**t1 {
                    Term::Abstraction(abstraction) => abstraction.substitute(t2),
                    _ => {
                        let t1_result = t1.reduce_one_step();
                        if t1_result.is_ok() {
                            return t1_result;
                        }
                        let t2_result = t2.reduce_one_step();
                        if t2_result.is_ok() {
                            return t2_result;
                        }
                        return Err(anyhow!(
                            "Had two options, neither of which worked out: {t1_result:?} and {t2_result:?}"
                        ));
                    }
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
                if x == variable {
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
pub struct Variable {
    inner: char,
    identifier: Option<usize>,
    lambda_type: Option<LambdaType>,
}

impl Variable {
    pub fn new(c: char) -> Self {
        Self {
            inner: c,
            identifier: None,
            lambda_type: None,
        }
    }

    pub fn set_type(&mut self, lambda_type: LambdaType) {
        self.lambda_type = Some(lambda_type);
    }

    pub fn set_identifier(&mut self, identifier: usize) {
        self.identifier = Some(identifier)
    }
}

impl Variable {
    fn erase_types(&mut self) {
        let Variable { inner: c, .. } = self;
        *self = Variable::new(*c)
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let var = self.inner;
        if let Some(identifier) = self.identifier {
            write!(f, "{var}_{identifier}")
        } else {
            var.fmt(f)
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum LambdaType {
    Boolean,
    Integer,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Abstraction {
    arg: Variable,
    body: Box<Term>,
    lambda_type: Option<LambdaType>,
}

impl Abstraction {
    fn new(arg: Variable, body: Term) -> Self {
        Self {
            arg,
            body: Box::new(body),
            lambda_type: None,
        }
    }

    fn new_with_type(arg: Variable, body: Term, lambda_type: LambdaType) -> Self {
        Self {
            arg,
            body: Box::new(body),
            lambda_type: Some(lambda_type),
        }
    }

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
        let mut body: Term = Term::Variable(Variable::new('z'));
        for _ in 0..value {
            body = Term::Application(Application(
                Box::new(Term::Variable(Variable::new('s'))),
                Box::new(body),
            ))
        }
        Term::Abstraction(Abstraction::new_with_type(
            Variable::new('s'),
            Term::Abstraction(Abstraction::new(Variable::new('z'), body)),
            LambdaType::Integer,
        ))
    }
}

impl TryFrom<Term> for bool {
    type Error = anyhow::Error;

    fn try_from(term: Term) -> Result<Self, Self::Error> {
        match term {
            Term::Abstraction(outer_abstraction) => {
                let inner_term = *outer_abstraction.body;
                match inner_term {
                    Term::Abstraction(inner_abstraction) => match *inner_abstraction.body {
                        Term::Variable(inner_variable) => {
                            if inner_variable == outer_abstraction.arg {
                                return Ok(true);
                            };
                            if inner_variable == inner_abstraction.arg {
                                return Ok(false);
                            };
                            Err(anyhow!("Last variable is not bound"))
                        }
                        _ => Err(anyhow!(
                            "Last term needs to be a variable {inner_abstraction}"
                        )),
                    },
                    _ => Err(anyhow!(
                        "Inner-term term needs to be an abstraction {inner_term}"
                    )),
                }
            }
            _ => Err(anyhow!("Outer-most term needs to be an abstraction {term}")),
        }
    }
}

impl TryFrom<Term> for u32 {
    type Error = anyhow::Error;

    fn try_from(mut term: Term) -> Result<Self, Self::Error> {
        let abstraction = match term {
            Term::Abstraction(abstraction) => abstraction,
            _ => return Err(anyhow!("root expected abstraction {term}")),
        };
        let var = abstraction.arg;
        let var = Term::Variable(var);
        term = *abstraction.body;

        term = match term {
            Term::Abstraction(abstraction) => *abstraction.body,
            _ => return Err(anyhow!("Second shell expected abstraction")),
        };

        let mut count = 0;
        while let Term::Application(application) = term {
            if *application.0 != var {
                return Err(anyhow!("Expected application of {var}"));
            }
            term = *application.1;
            count += 1;
        }
        match term {
            Term::Variable(..) => {}
            _ => return Err(anyhow!("First non-application not a variable {term}")),
        };
        Ok(count)
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::parsing::parse_term;

    #[test]
    fn identity() {
        let identity = Term::Abstraction(Abstraction::new(
            Variable::new('x'),
            Term::Variable(Variable::new('x')),
        ));
        assert_eq!("λx.x", format!("{identity}"))
    }

    #[test]
    fn test_true() {
        let lambda_true = Term::Abstraction(Abstraction::new(
            Variable::new('x'),
            Term::Abstraction(Abstraction::new(
                Variable::new('y'),
                Term::Variable(Variable::new('x')),
            )),
        ));
        assert_eq!("λx.λy.x", format!("{lambda_true}"));
        let typed_true: bool = lambda_true.try_into().unwrap();
        assert!(typed_true);
    }

    #[test]
    fn test_false() {
        let lambda_false = Term::Abstraction(Abstraction::new(
            Variable::new('x'),
            Term::Abstraction(Abstraction::new(
                Variable::new('y'),
                Term::Variable(Variable::new('y')),
            )),
        ));
        assert_eq!("λx.λy.y", format!("{lambda_false}"));
        let typed_false: bool = lambda_false.try_into().unwrap();
        assert!(!typed_false);
    }

    #[test]
    fn ambiguous_association() {
        // Application is left associative per default
        let left_associative = Term::Application(Application(
            Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable::new('x'))),
                Box::new(Term::Variable(Variable::new('y'))),
            ))),
            Box::new(Term::Variable(Variable::new('z'))),
        ));

        // This one needs parenthesis to disambiguate
        let right_associative = Term::Application(Application(
            Box::new(Term::Variable(Variable::new('x'))),
            Box::new(Term::Application(Application(
                Box::new(Term::Variable(Variable::new('y'))),
                Box::new(Term::Variable(Variable::new('z'))),
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
            Box::new(Term::Abstraction(Abstraction::new(
                Variable::new('x'),
                Term::Variable(Variable::new('y')),
            ))),
            Box::new(Term::Variable(Variable::new('z'))),
        ));
        let term_2 = Term::Abstraction(Abstraction::new(
            Variable::new('x'),
            Term::Application(Application(
                Box::new(Term::Variable(Variable::new('y'))),
                Box::new(Term::Variable(Variable::new('z'))),
            )),
        ));

        assert_ne!(format!("{term_1}"), format!("{term_2}"));
    }

    #[test]
    fn test_reduction_of_true() {
        let mut term = parse_term("(λx.λy.x) a b").unwrap();
        term.reduce();
        assert_eq!(term, parse_term("a").unwrap());
    }

    #[test]
    fn test_reduction_of_false() {
        let mut term = parse_term("(λx.λy.y) a b").unwrap();
        term.reduce();
        assert_eq!(term, parse_term("b").unwrap());
    }

    #[test]
    fn converting_between_nat_and_lambda_representation() {
        for i in 0..100 {
            let term: Term = i.into();
            let nat = term.try_into().unwrap();
            assert_eq!(i, nat);
        }
    }

    #[test]
    fn addition() {
        for i in 0..10 {
            for j in 0..10 {
                let plus: Term = parse_term("λm.λn.λf.λx.m f (n f x)").unwrap();
                let mut addition_expression: Term =
                    parsing::parse_term(&format!("({plus}) ({i}) ({j})")).unwrap();
                addition_expression.reduce();
                let result: u32 = addition_expression.try_into().unwrap();
                assert_eq!(i + j, result);
            }
        }
    }

    #[test]
    fn multiplication() {
        for i in 0..10 {
            for j in 0..10 {
                let multiply: Term = parse_term("λm.λn.λf.m (n f)").unwrap();
                let mut multiplication_expression: Term =
                    parsing::parse_term(&format!("({multiply}) ({i}) ({j})")).unwrap();
                multiplication_expression.reduce();
                let result: u32 = multiplication_expression.try_into().unwrap();
                assert_eq!(i * j, result);
            }
        }
    }

    #[test]
    fn factorial() {
        let factorial: Term =
            parse_term("λk.k(λp.p(λabg.g(λfx.f(afx))(λf.a(bf))))(λg.g(λh.h)(λh.h))(λab.b)")
                .unwrap();
        let mut five_factorial: Term = parsing::parse_term(&format!("({factorial}) 5")).unwrap();
        five_factorial.reduce();
        let result: u32 = five_factorial.try_into().unwrap();
        assert_eq!(120, result);
    }
}

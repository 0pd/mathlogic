use std::fmt::{Formatter, Display, Debug};
use std::ops::{BitAnd, BitOr, Not};

pub fn parse(line: &str) -> Result<Node, Error> {
    let mut scanner = Scanner::new(line);
    parse_imply(&mut scanner).and_then(|node| {
        if scanner.is_end() {
            Ok(node)
        } else {
            Err(Error::Character(scanner.cursor))
        }
    })
}

#[derive(PartialEq, Debug)]
pub enum Error {
    Character(usize),
    EndOfLine(),
}

#[derive(Eq, PartialEq, Hash)]
pub enum Node {
    Var(String),
    Not(Box<Node>),
    And(Box<Node>, Box<Node>),
    Or(Box<Node>, Box<Node>),
    Imply(Box<Node>, Box<Node>),
}

impl Node {
    pub(crate) fn var(name: &str) -> Node {
        Node::Var(name.to_string())
    }

    pub(crate) fn imply(lhs: Node, rhs: Node) -> Node {
        Node::Imply(Box::new(lhs), Box::new(rhs))
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Node::Var(name) => {
                write!(f, "{}", name)
            }
            Node::Not(node) => {
                write!(f, "({})", node)
            }
            Node::And(lhs, rhs) => {
                write!(f, "(&,{},{})", lhs, rhs)
            }
            Node::Or(lhs, rhs) => {
                write!(f, "(|,{},{})", lhs, rhs)
            }
            Node::Imply(lhs, rhs) => {
                write!(f, "(->,{},{})", lhs, rhs)
            }
        }
    }
}

impl Debug for Node {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Not for Node {
    type Output = Node;

    fn not(self) -> Self::Output {
        Node::Not(Box::new(self))
    }
}

impl BitAnd for Node {
    type Output = Node;

    fn bitand(self, rhs: Self) -> Self::Output {
        Node::And(Box::new(self), Box::new(rhs))
    }
}

impl BitOr for Node {
    type Output = Node;

    fn bitor(self, rhs: Self) -> Self::Output {
        Node::Or(Box::new(self), Box::new(rhs))
    }
}

fn parse_imply(scanner: &mut Scanner) -> Result<Node, Error> {
    parse_or(scanner).and_then(|lhs| {
        if scanner.take("->").is_ok() {
            parse_imply(scanner).map(|rhs| Node::imply(lhs, rhs))
        } else {
            Ok(lhs)
        }
    })
}

fn parse_or(scanner: &mut Scanner) -> Result<Node, Error> {
    parse_and(scanner).and_then(|lhs| {
        if scanner.take("|").is_ok() {
            parse_or(scanner).map(|rhs| lhs | rhs)
        } else {
            Ok(lhs)
        }
    })
}

fn parse_and(scanner: &mut Scanner) -> Result<Node, Error> {
    let mut acc = parse_not(scanner);
    while scanner.take("&").is_ok() {
        acc = acc.and_then(|lhs| parse_not(scanner).map(|rhs| lhs & rhs));
    }

    acc
}

fn parse_not(scanner: &mut Scanner) -> Result<Node, Error> {
    match scanner.peek() {
        Some('!') => {
            scanner.pop();
            parse_not(scanner).map(|r| !r)
        }
        Some('(') => {
            scanner.pop();
            parse_imply(scanner).and_then(|expr| scanner.take(")").map(|_| expr))
        }
        Some(_) => parse_var(scanner),
        None => Err(Error::EndOfLine()),
    }
}

fn parse_var(scanner: &mut Scanner) -> Result<Node, Error> {
    let mut name = String::new();
    while let Some(c) = scanner.peek() {
        if c >= &'A' && c <= &'Z' || c >= &'0' && c <= &'9' {
            name.push(*c);

            scanner.pop();
        } else {
            break;
        }
    }

    if name.is_empty() {
        Err(Error::Character(scanner.cursor))
    } else {
        Ok(Node::var(&name))
    }
}

struct Scanner {
    cursor: usize,
    chars: Vec<char>,
}

impl Scanner {
    fn new(string: &str) -> Scanner {
        Scanner {
            cursor: 0,
            chars: string.chars().collect(),
        }
    }

    fn take_char(&mut self, target: &char) -> Result<(), Error> {
        match self.peek() {
            Some(character) => {
                if target == character {
                    self.cursor += 1;

                    Ok(())
                } else {
                    Err(Error::Character(self.cursor))
                }
            }
            None => Err(Error::Character(self.cursor)),
        }
    }

    fn take(&mut self, target: &str) -> Result<(), Error> {
        for char in target.chars() {
            match self.take_char(&char) {
                Ok(_) => {}
                Err(error) => {
                    return Err(error);
                }
            }
        }

        Ok(())
    }

    fn peek(&self) -> Option<&char> {
        self.chars.get(self.cursor)
    }

    fn pop(&mut self) -> Option<&char> {
        match self.chars.get(self.cursor) {
            Some(c) => {
                self.cursor += 1;

                Some(c)
            }
            None => None,
        }
    }

    fn is_end(&self) -> bool {
        self.chars.len() == self.cursor
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_end_of_line() {
        let line = "!";
        let should_fail = parse(line);
        assert!(should_fail.is_err());
        assert_eq!(should_fail.unwrap_err(), Error::EndOfLine())
    }

    #[test]
    fn parse_character() {
        let line = "P/Q";
        let should_fail = parse(line);
        assert!(should_fail.is_err());
        assert_eq!(should_fail.unwrap_err(), Error::Character(1))
    }

    #[test]
    fn parse_var() {
        let line = "P";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::var("P"));
    }

    #[test]
    fn parse_var_long_name() {
        let line = "P10";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::var("P10"));
    }

    #[test]
    fn parse_not() {
        let line = "!P";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), !Node::var("P"));
    }

    #[test]
    fn parse_and() {
        let line = "P&Q";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::var("P") & Node::var("Q"));
    }

    #[test]
    fn parse_and_and() {
        let line = "P&Q&R";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::var("P") & Node::var("Q") & Node::var("R"));
    }

    #[test]
    fn parse_or() {
        let line = "P|Q";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::var("P") | Node::var("Q"));
    }

    #[test]
    fn parse_imply() {
        let line = "P->Q";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::imply(Node::var("P"), Node::var("Q")));
    }

    #[test]
    fn parse_with_brackets() {
        let line = "!(P->Q)";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), !Node::imply(Node::var("P"), Node::var("Q")));
    }

    #[test]
    fn parse_not_so_complex() {
        let line = "!R11&S|!T&U&V";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(
            result.unwrap(),
            !Node::var("R11") & Node::var("S") | !Node::var("T") & Node::var("U") & Node::var("V")
        );
    }

    #[test]
    fn parse_complex_expression() {
        let line = "P->!QQ->!R10&S|!T&U&V";
        let result = parse(line);
        assert!(result.is_ok());
        assert_eq!(
            result.unwrap(),
            Node::imply(
                Node::var("P"),
                Node::imply(
                    !Node::var("QQ"),
                    !Node::var("R10") & Node::var("S") | !Node::var("T") & Node::var("U") & Node::var("V"),
                ),
            )
        );
    }
}

use std::fmt;

pub fn parse(line: &str) -> Node {
    let mut scanner = Scanner::new(line);
    parse_imply(&mut scanner).unwrap()
}

#[derive(Debug)]
pub enum Error {
    Character(usize),
}

#[derive(Eq, PartialEq)]
pub enum Node {
    Var(String),
    UnaryExpr {
        op: Operator,
        child: Box<Node>,
    },
    BinaryExpr {
        op: Operator,
        lhs: Box<Node>,
        rhs: Box<Node>,
    },
}

impl Node {
    fn var(name: &str) -> Node {
        Node::Var(name.to_string())
    }

    fn not(node: Node) -> Node {
        Node::UnaryExpr {
            op: Operator::Not,
            child: Box::new(node),
        }
    }

    fn and(lhs: Node, rhs: Node) -> Node {
        Node::binary(Operator::And, lhs, rhs)
    }

    fn or(lhs: Node, rhs: Node) -> Node {
        Node::binary(Operator::Or, lhs, rhs)
    }

    fn imply(lhs: Node, rhs: Node) -> Node {
        Node::binary(Operator::Imply, lhs, rhs)
    }

    fn binary(op: Operator, lhs: Node, rhs: Node) -> Node {
        Node::BinaryExpr {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Node::Var(name) => {
                write!(f, "{}", name)
            }
            Node::UnaryExpr { op, child } => {
                write!(f, "({:?}{:?})", op, child)
            }
            Node::BinaryExpr { op, lhs, rhs } => {
                write!(f, "({:?},{:?},{:?})", op, lhs, rhs)
            }
        }
    }
}

#[derive(Eq, PartialEq)]
pub enum Operator {
    Not,
    And,
    Or,
    Imply,
}

impl fmt::Debug for Operator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let sign = match self {
            Operator::Not => "!",
            Operator::And => "&",
            Operator::Or => "|",
            Operator::Imply => "->",
        };

        write!(f, "{}", sign)
    }
}

fn parse_imply(scanner: &mut Scanner) -> Result<Node, Error> {
    parse_or(scanner).and_then(|lhs| match scanner.peek() {
        Some('-') => {
            scanner.pop();
            match scanner.pop() {
                Some('>') => parse_imply(scanner).map(|rhs| Node::imply(lhs, rhs)),
                _ => {
                    unimplemented!()
                }
            }
        }
        _ => Ok(lhs),
    })
}

fn parse_or(scanner: &mut Scanner) -> Result<Node, Error> {
    parse_and(scanner).and_then(|lhs| match scanner.peek() {
        Some('|') => {
            scanner.pop();
            parse_or(scanner).map(|rhs| Node::or(lhs, rhs))
        }
        _ => Ok(lhs),
    })
}

fn parse_and(scanner: &mut Scanner) -> Result<Node, Error> {
    let lhs = parse_not(scanner);
    let mut acc = lhs;
    while let Some('&') = scanner.peek() {
        scanner.pop();
        acc = acc.and_then(|a| parse_not(scanner).map(|rhs| Node::and(a, rhs)));
    }
    acc
}

fn parse_not(scanner: &mut Scanner) -> Result<Node, Error> {
    match scanner.peek() {
        Some('!') => {
            scanner.pop();
            parse_not(scanner).map(|r| Node::not(r))
        }
        Some('(') => {
            scanner.pop();
            let expr = parse_imply(scanner);
            match scanner.pop() {
                Some(')') => expr,
                _ => unimplemented!(),
            }
        }
        Some(_) => parse_var(scanner),
        None => todo!(),
    }
}

fn parse_var(scanner: &mut Scanner) -> Result<Node, Error> {
    let mut acc = String::new();
    while let Some(c) = scanner.peek() {
        if c >= &'A' && c <= &'Z' || c >= &'0' && c <= &'9' {
            acc.push(*c);
            scanner.pop();
        } else {
            break;
        }
    }

    if acc.is_empty() {
        Err(Error::Character(scanner.cursor))
    } else {
        Ok(Node::var(&acc))
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_var() {
        let line = "P";
        assert_eq!(Node::var("P"), parse(line));
    }

    #[test]
    fn parse_var_long_name() {
        let line = "P10";
        assert_eq!(Node::var("P10"), parse(line));
    }

    #[test]
    fn parse_not() {
        let line = "!P";
        assert_eq!(Node::not(Node::var("P")), parse(line));
    }

    #[test]
    fn parse_and() {
        let line = "P&Q";
        assert_eq!(Node::and(Node::var("P"), Node::var("Q")), parse(line));
    }

    #[test]
    fn parse_and_and() {
        let line = "P&Q&R";
        assert_eq!(
            Node::and(Node::and(Node::var("P"), Node::var("Q")), Node::var("R")),
            parse(line)
        );
    }

    #[test]
    fn parse_or() {
        let line = "P|Q";
        assert_eq!(Node::or(Node::var("P"), Node::var("Q")), parse(line));
    }

    #[test]
    fn parse_imply() {
        let line = "P->Q";
        assert_eq!(Node::imply(Node::var("P"), Node::var("Q")), parse(line));
    }

    #[test]
    fn parse_with_brackets() {
        let line = "!(P->Q)";
        assert_eq!(
            Node::not(Node::imply(Node::var("P"), Node::var("Q"))),
            parse(line)
        );
    }

    #[test]
    fn parse_not_so_complex() {
        let line = "!R11&S|!T&U&V";
        assert_eq!(
            Node::or(
                Node::and(Node::not(Node::var("R11")), Node::var("S")),
                Node::and(
                    Node::and(Node::not(Node::var("T")), Node::var("U")),
                    Node::var("V")
                ),
            ),
            parse(line)
        );
    }

    #[test]
    fn parse_complex_expression() {
        let line = "P->!QQ->!R10&S|!T&U&V";
        assert_eq!(
            Node::imply(
                Node::var("P"),
                Node::imply(
                    Node::not(Node::var("QQ")),
                    Node::or(
                        Node::and(Node::not(Node::var("R10")), Node::var("S")),
                        Node::and(
                            Node::and(Node::not(Node::var("T")), Node::var("U")),
                            Node::var("V"),
                        ),
                    ),
                ),
            ),
            parse(line)
        );
    }
}

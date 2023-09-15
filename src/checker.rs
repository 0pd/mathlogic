use crate::parser::{Node, Operator};

// A->B->A
fn check_axiom1(node: &Node) -> bool {
    match node {
        Node::BinaryExpr { op: Operator::Imply, lhs, rhs } => {
            check_binary(rhs, Operator::Imply, |_, b| b.eq(lhs))
        }
        _ => false
    }
}

// (A->B)->(A->B->C)->(A->C)
fn check_axiom2(node: &Node) -> bool {
    unimplemented!()
}

// A->B->A&B
fn check_axiom3(node: &Node) -> bool {
    match node {
        Node::BinaryExpr { op: Operator::Imply, lhs, rhs } => {
            check_binary(rhs, Operator::Imply, |a, b| {
                check_binary(b, Operator::And, |c, d| {
                    c.eq(lhs) && d.eq(a)
                })
            })
        }
        _ => false
    }
}

// A&B->A
// A&B->B
fn check_axiom45(node: &Node) -> bool {
    match node {
        Node::BinaryExpr { op: Operator::Imply, lhs, rhs } => {
            check_binary(lhs, Operator::And, |a, b| a.eq(rhs) || b.eq(rhs))
        }
        _ => false
    }
}

// A->A|B
// B->A|B
fn check_axiom67(node: &Node) -> bool {
    match node {
        Node::BinaryExpr { op: Operator::Imply, lhs, rhs } => {
            check_binary(rhs, Operator::Or, |a, b| a.eq(lhs) || b.eq(lhs))
        }
        _ => false
    }
}

// (A->C)->(B->C)->(A|B->C)
fn check_axiom8(node: &Node) -> bool {
    unimplemented!()
}

// (A->B)->(A->!B)->!A
fn check_axiom9(node: &Node) -> bool {
    unimplemented!()
}

// !!A->A
fn check_axiom10(node: &Node) -> bool {
    fn check(node: &Node) -> bool {
        if let Node::UnaryExpr { op: Operator::Not, child: _ } = node {
            true
        } else {
            false
        }
    }

    match node {
        Node::UnaryExpr { op: Operator::Not, child } => check(child),
        _ => false
    }
}

fn check_binary<F>(node: &Node, operator: Operator, func: F) -> bool
    where F: FnOnce(&Node, &Node) -> bool {
    match node {
        Node::BinaryExpr { op, lhs, rhs } if operator.eq(op) => func(lhs, rhs),
        _ => false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    #[test]
    fn test_axiom1_simple() {
        let expr = parse("A->B->A").unwrap();
        assert!(check_axiom1(&expr));
    }

    #[test]
    fn test_axiom1_not() {
        let expr = parse("!A->B->!A").unwrap();
        assert!(check_axiom1(&expr));
    }

    #[test]
    fn test_axiom1_complex() {
        let expr = parse("!(A&B)->(B|C|D)->!(A&B)").unwrap();
        assert!(check_axiom1(&expr));
    }

    #[test]
    fn test_axiom3() {
        let expr = parse("A->B->A&B").unwrap();
        assert!(check_axiom3(&expr));
    }

    #[test]
    fn test_axiom4() {
        let expr = parse("A&B->A").unwrap();
        assert!(check_axiom45(&expr));
    }

    #[test]
    fn test_axiom5() {
        let expr = parse("A&B->B").unwrap();
        assert!(check_axiom45(&expr));
    }

    #[test]
    fn test_axiom6() {
        let expr = parse("A->A|B").unwrap();
        assert!(check_axiom67(&expr));
    }

    #[test]
    fn test_axiom7() {
        let expr = parse("B->A|B").unwrap();
        assert!(check_axiom67(&expr));
    }

    #[test]
    fn test_axiom10() {
        let expr = parse("!!A").unwrap();
        assert!(check_axiom10(&expr));
    }
}
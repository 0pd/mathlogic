use crate::parser::{Node, Operator};

// A->B->A
fn check_axiom1(node: &Node) -> bool {
    check_binary(node, Operator::Imply, |ant, cons| {
        check_binary(cons, Operator::Imply, |_, inner_cons| {
            inner_cons.eq(ant)
        })
    })
}

// (A->B)->(A->B->C)->(A->C)
fn check_axiom2(node: &Node) -> bool {
    check_binary(node, Operator::Imply, |ant, cons| {
        check_binary(cons, Operator::Imply, |inner_ant, inner_cons| {
            check_binary(ant, Operator::Imply, |a1, b1| {
                check_binary(inner_ant, Operator::Imply, |a2, inner_inner_cons| {
                    a1.eq(a2) && check_binary(inner_inner_cons, Operator::Imply, |b2, c2| {
                        b1.eq(b2) && check_binary(inner_cons, Operator::Imply, |a3, c3| {
                            a1.eq(a3) && c2.eq(c3)
                        })
                    })
                })
            })
        })
    })
}

// A->B->A&B
fn check_axiom3(node: &Node) -> bool {
    check_binary(node, Operator::Imply, |ant, cons| {
        check_binary(cons, Operator::Imply, |inner_ant, inner_cons| {
            check_binary(inner_cons, Operator::And, |lhs, rhs| {
                lhs.eq(ant) && rhs.eq(inner_ant)
            })
        })
    })
}

// A&B->A
// A&B->B
fn check_axiom45(node: &Node) -> bool {
    check_binary(node, Operator::Imply, |ant, cons| {
        check_binary(ant, Operator::And, |lhs, rhs| {
            lhs.eq(cons) || rhs.eq(cons)
        })
    })
}

// A->A|B
// B->A|B
fn check_axiom67(node: &Node) -> bool {
    check_binary(node, Operator::Imply, |ant, cons| {
        check_binary(cons, Operator::Or, |lhs, rhs| {
            lhs.eq(ant) || rhs.eq(ant)
        })
    })
}

// (A->C)->(B->C)->(A|B->C)
fn check_axiom8(node: &Node) -> bool {
    check_binary(node, Operator::Imply, |ant, cons| {
        check_binary(cons, Operator::Imply, |inner_ant, inner_cons| {
            check_binary(ant, Operator::Imply, |a1, c1| {
                check_binary(inner_ant, Operator::Imply, |b2, c2| {
                    c1.eq(c2) && check_binary(inner_cons, Operator::Imply, |inner_inner_ant, c3| {
                        c1.eq(c3) && check_binary(inner_inner_ant, Operator::Or, |a3, b3| {
                            a1.eq(a3) && b2.eq(b3)
                        })
                    })
                })
            })
        })
    })
}

// (A->B)->(A->!B)->!A
fn check_axiom9(node: &Node) -> bool {
    fn check_not(node: &Node, negative: &Node) -> bool {
        if let Node::UnaryExpr { op: Operator::Not, child } = negative {
            node.eq(child)
        } else {
            false
        }
    }

    check_binary(node, Operator::Imply, |ant, cons| {
        check_binary(cons, Operator::Imply, |inner_ant, not_a3| {
            check_binary(ant, Operator::Imply, |a1, b1| {
                check_binary(inner_ant, Operator::Imply, |a2, not_b2| {
                    a1.eq(a2) && check_not(a1, not_a3) && check_not(b1, not_b2)
                })
            })
        })
    })
}

// !!A->A
fn check_axiom10(node: &Node) -> bool {
    match node {
        Node::UnaryExpr { op: Operator::Not, child } => {
            if let Node::UnaryExpr { op: Operator::Not, child: _ } = **child {
                true
            } else {
                false
            }
        }
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
    fn test_axiom2() {
        let expr = parse("(A->B)->(A->B->C)->(A->C)").unwrap();
        assert!(check_axiom2(&expr));
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
    fn test_axiom8() {
        let expr = parse("(A->C)->(B->C)->(A|B->C)").unwrap();
        assert!(check_axiom8(&expr));
    }

    #[test]
    fn test_axiom9() {
        let expr = parse("(A->B)->(A->!B)->!A").unwrap();
        assert!(check_axiom9(&expr));
    }

    #[test]
    fn test_axiom10() {
        let expr = parse("!!A").unwrap();
        assert!(check_axiom10(&expr));
    }
}
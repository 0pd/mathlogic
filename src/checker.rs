use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use crate::parser::Node;

pub fn check(assumptions: &[Node], proof: &[Node]) -> Vec<Status> {
    let mut result = vec![];
    let assumptions_set: HashMap<&Node, u32> = HashMap::from_iter(assumptions.iter().enumerate().map(|(i, x)| (x, (i + 1) as u32)));
    let mut proven = HashMap::new();
    let mut potential: HashMap<String, Vec<(String, u32)>> = HashMap::new();
    for (index, statement) in proof.iter().enumerate() {
        let status = if let Some(i) = assumptions_set.get(statement) {
            Status::Assumption(*i)
        } else if let Some(i) = check_axioms(statement) {
            Status::AxiomSchema(i)
        } else if let Some((i, j)) = check_mp(statement, &proven, &potential) {
            Status::MP(i, j)
        } else {
            Status::NotProven
        };

        if status != Status::NotProven {
            proven.insert(statement.to_string(), index as u32);

            if let Node::Imply(lhs, rhs) = statement {
                let ant = lhs.to_string();
                let cons = rhs.to_string();
                if let Some(entry) = potential.get_mut(&cons) {
                    entry.push((ant, index as u32));
                } else {
                    potential.insert(cons, vec![(ant, index as u32)]);
                }
            }
        }

        result.push(status);
    }

    result
}

#[derive(PartialEq, Debug)]
pub enum Status {
    AxiomSchema(u32),
    Assumption(u32),
    MP(u32, u32),
    NotProven,
}

impl Display for Status {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Status::AxiomSchema(i) => {
                write!(f, "Axiom Schema {}", i)
            }
            Status::Assumption(i) => {
                write!(f, "Assumption {}", i)
            }
            Status::MP(i, j) => {
                write!(f, "M.P. {}, {}", i, j)
            }
            Status::NotProven => {
                write!(f, "Not proven")
            }
        }
    }
}

fn check_mp(node: &Node, proven: &HashMap<String, u32>, potential: &HashMap<String, Vec<(String, u32)>>) -> Option<(u32, u32)> {
    let s = node.to_string();
    if let Some(entry) = potential.get(&s) {
        for (ant, index) in entry {
            if let Some(proven_index) = proven.get(ant) {
                return Some((*index + 1, *proven_index + 1));
            }
        }
    }

    None
}

fn check_axioms(node: &Node) -> Option<u32> {
    if check_axiom1(node) {
        Some(1)
    } else if check_axiom2(node) {
        Some(2)
    } else if check_axiom3(node) {
        Some(3)
    } else if check_axiom45(node) {
        Some(45)
    } else if check_axiom67(node) {
        Some(67)
    } else if check_axiom8(node) {
        Some(8)
    } else if check_axiom9(node) {
        Some(9)
    } else if check_axiom10(node) {
        Some(10)
    } else {
        None
    }
}

// A->B->A
fn check_axiom1(node: &Node) -> bool {
    if let Node::Imply(ant, cons) = node {
        if let Node::Imply(_, inner_cons) = &**cons {
            return inner_cons.eq(ant);
        }
    }

    false
}

// (A->B)->(A->B->C)->(A->C)
fn check_axiom2(node: &Node) -> bool {
    if let Node::Imply(ant, cons) = node {
        if let Node::Imply(inner_ant, inner_cons) = &**cons {
            if let Node::Imply(a1, b1) = &**ant {
                if let Node::Imply(a2, inner_inner_cons) = &**inner_ant {
                    if let Node::Imply(b2, c2) = &**inner_inner_cons {
                        if let Node::Imply(a3, c3) = &**inner_cons {
                            return a1.eq(a2) && b1.eq(b2) && a1.eq(a3) && c2.eq(c3);
                        }
                    }
                }
            }
        }
    }

    false
}

// A->B->A&B
fn check_axiom3(node: &Node) -> bool {
    if let Node::Imply(ant, cons) = node {
        if let Node::Imply(inner_ant, inner_cons) = &**cons {
            if let Node::And(lhs, rhs) = &**inner_cons {
                return lhs.eq(ant) && rhs.eq(inner_ant);
            }
        }
    }

    false
}

// A&B->A
// A&B->B
fn check_axiom45(node: &Node) -> bool {
    if let Node::Imply(ant, cons) = node {
        if let Node::And(lhs, rhs) = &**ant {
            return lhs.eq(cons) || rhs.eq(cons);
        }
    }

    false
}

// A->A|B
// B->A|B
fn check_axiom67(node: &Node) -> bool {
    if let Node::Imply(ant, cons) = node {
        if let Node::Or(lhs, rhs) = &**cons {
            return lhs.eq(ant) || rhs.eq(ant);
        }
    }

    false
}

// (A->C)->(B->C)->(A|B->C)
fn check_axiom8(node: &Node) -> bool {
    if let Node::Imply(ant, cons) = node {
        if let Node::Imply(inner_ant, inner_cons) = &**cons {
            if let Node::Imply(a1, c1) = &**ant {
                if let Node::Imply(b2, c2) = &**inner_ant {
                    if let Node::Imply(inner_inner_ant, c3) = &**inner_cons {
                        if let Node::Or(a3, b3) = &**inner_inner_ant {
                            return c1.eq(c3) && c1.eq(c2) && a1.eq(a3) && b2.eq(b3);
                        }
                    }
                }
            }
        }
    }

    false
}

// (A->B)->(A->!B)->!A
fn check_axiom9(node: &Node) -> bool {
    fn check_not(node: &Node, negative: &Node) -> bool {
        if let Node::Not(inner_node) = negative {
            node.eq(inner_node)
        } else {
            false
        }
    }

    if let Node::Imply(ant, cons) = node {
        if let Node::Imply(inner_ant, not_a3) = &**cons {
            if let Node::Imply(a1, b1) = &**ant {
                if let Node::Imply(a2, not_b2) = &**inner_ant {
                    return a1.eq(a2) && check_not(a1, not_a3) && check_not(b1, not_b2);
                }
            }
        }
    }

    false
}

// !!A->A
fn check_axiom10(node: &Node) -> bool {
    if let Node::Imply(ant, cons) = node {
        if let Node::Not(not) = &**ant {
            if let Node::Not(inner_not) = &**not {
                return cons.eq(inner_not);
            }
        }
    }

    false
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
        let expr = parse("!!A->A").unwrap();
        assert!(check_axiom10(&expr));
    }

    #[test]
    fn test_check() {
        let assumptions = ["A", "B"].iter().map(|s| parse(s).unwrap()).collect::<Vec<Node>>();
        let proof = ["A", "B", "A->B->A&B", "B->A&B", "A&B"].iter().map(|s| parse(s).unwrap()).collect::<Vec<Node>>();
        let result = check(&assumptions, &proof);
        let expected = vec![
            Status::Assumption(1),
            Status::Assumption(2),
            Status::AxiomSchema(3),
            Status::MP(3, 1),
            Status::MP(4, 2),
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_check2() {
        let assumptions = ["A", "B"].iter().map(|s| parse(s).unwrap()).collect::<Vec<Node>>();
        let proof = ["A", "B", "(A->(B->(A&B)))", "(B->(A&B))", "(A->A)", "(A&B)"].iter().map(|s| parse(s).unwrap()).collect::<Vec<Node>>();
        let result = check(&assumptions, &proof);
        let expected = vec![
            Status::Assumption(1),
            Status::Assumption(2),
            Status::AxiomSchema(3),
            Status::MP(3, 1),
            Status::NotProven,
            Status::MP(4, 2),
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_check3() {
        let assumptions = vec![];
        let proof = ["(A->A->A)->(A->(A->A)->A)->(A->A)", "(A->A->A)", "(A->(A->A)->A)", "(A->(A->A)->A)->(A->A)", "A->A"].iter().map(|s| parse(s).unwrap()).collect::<Vec<Node>>();
        let result = check(&assumptions, &proof);
        let expected = vec![
            Status::AxiomSchema(2),
            Status::AxiomSchema(1),
            Status::AxiomSchema(1),
            Status::MP(1, 2),
            Status::MP(4, 3),
        ];
        assert_eq!(result, expected);
    }

    // This differs from the task's requirements
    // A statement cannot be proven if it implies from a statement that is not proven
    #[test]
    fn test_check4() {
        let assumptions = vec![];
        let proof = ["(A->B)", "A", "B"].iter().map(|s| parse(s).unwrap()).collect::<Vec<Node>>();
        let result = check(&assumptions, &proof);
        let expected = vec![
            Status::NotProven,
            Status::NotProven,
            Status::NotProven,
        ];
        assert_eq!(result, expected);
    }
}
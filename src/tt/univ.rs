use std::ops::{Add, Sub, AddAssign, SubAssign, Neg};
use std::fmt::{Display, Formatter, Result as FmtResult};
use miette::{Result as MResult, bail};
use petgraph::{
    Direction,
    algo::{FloatMeasure, bellman_ford::find_negative_cycle},
    graph::{DiGraph, NodeIndex},
    dot::Dot,
    visit::EdgeRef,
};
use super::{DeBruijn, SDeBruijn};

/// A constant universe level.
///
/// There is an infinite hierarchy of universe levels. They start at `0`, `1`, `2`, ... and continue
/// to `ω`. Then there's `ω+1`, `ω+2`, ... until `ω*2`, `ω*2 + 1`, etc. This continues until *and
/// not including* `ω²`.
///
/// It is important to note that these are *not* ordinals: `ω-1` is perfectly well defined. This is
/// more akin to [https://wikipedia.org/wiki/Hyperinteger](hyperintegers).
///
/// As an implementation detail, we allow negative levels. This is simply so we can create
/// difference constraints with them. All levels are constrained to be nonnegative by the constraint
/// checker.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Level {
    pub omega: i32,
    pub extra: i32,
}

impl Level {
    pub const fn new(omega: i32, extra: i32) -> Self {
        Level { omega, extra }
    }
}

impl Display for Level {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        if self.omega == 0 {
            self.extra.fmt(f)
        } else if self.extra == 0 {
            write!(f, "{}ω", self.omega)
        } else if self.extra > 0 {
            write!(f, "{}ω + {}", self.omega, self.extra)
        } else {
            write!(f, "{}ω - {}", self.omega, -self.extra)
        }
    }
}

impl AddAssign for Level {
    fn add_assign(&mut self, rhs: Self) {
        self.omega += rhs.omega;
        self.extra += rhs.extra;
    }
}

impl SubAssign for Level {
    fn sub_assign(&mut self, rhs: Self) {
        self.omega -= rhs.omega;
        self.extra -= rhs.extra;
    }
}

impl Add for Level {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl Sub for Level {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl AddAssign<i32> for Level {
    fn add_assign(&mut self, rhs: i32) {
        self.extra += rhs;
    }
}

impl SubAssign<i32> for Level {
    fn sub_assign(&mut self, rhs: i32) {
        self.extra -= rhs;
    }
}

impl Add<i32> for Level {
    type Output = Self;

    fn add(mut self, rhs: i32) -> Self::Output {
        self += rhs;
        self
    }
}

impl Sub<i32> for Level {
    type Output = Self;

    fn sub(mut self, rhs: i32) -> Self::Output {
        self -= rhs;
        self
    }
}

impl Neg for Level {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Level {
            omega: -self.omega,
            extra: -self.extra,
        }
    }
}

impl From<i32> for Level {
    fn from(extra: i32) -> Self {
        Level { omega: 0, extra }
    }
}

impl FloatMeasure for Level {
    fn zero() -> Self {
        Self::default()
    }

    fn infinite() -> Self {
        Level {
            omega: 10_000_000,
            extra: 0,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct Var(u32);

impl From<NodeIndex<u32>> for Var {
    fn from(n: NodeIndex<u32>) -> Self {
        Var(n.index() as u32)
    }
}

impl From<Var> for NodeIndex<u32> {
    fn from(v: Var) -> Self {
        NodeIndex::new(v.0 as usize)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Term {
    Var(DeBruijn, Var),
    Add(Box<Term>, Level),
    Max(Vec<Term>),
    Min(Vec<Term>),
}

impl Term {
    fn sort_max_min(&mut self) {
        if let Term::Max(ts) | Term::Min(ts) = self {
            for t in ts.iter_mut() {
                t.sort_max_min();
            }
            ts.sort_unstable();
            ts.dedup();
        }
    }

    fn desingleton_max_min(&mut self) {
        match self {
            Term::Var(..) => (),
            Term::Add(t, _) => {
                t.desingleton_max_min();
            },
            Term::Max(ts) | Term::Min(ts) => if let [t] = ts.as_mut_slice() { unsafe {
                let t = (t as *const Term).read();
                (self as *mut Term).write(t);
                self.desingleton_max_min();
            } } else {
                for t in ts {
                    t.desingleton_max_min();
                }
            },
        }
    }

    fn fold_add(&mut self) {
        match self {
            Term::Var(..) => return,
            Term::Add(t, l) => {
                let tp = t as *mut _;
                match t.as_mut() {
                    &mut Term::Var(db, v) => if *l == Level::default() {
                        *self = Term::Var(db, v);
                    },
                    Term::Add(t2, l2) => {
                        *l += *l2;
                        unsafe { replace_new_and_drop(tp, t2) };
                        self.fold_add();
                    },
                    Term::Max(ts) => unsafe {
                        for t in ts.iter_mut() {
                            let tp = t as *mut Term;
                            tp.write(Term::Add(tp.read().into(), *l));
                            t.fold_add();
                        }
                        let ts = std::mem::take(ts);
                        drop_as_manually_drop(tp.read());
                        (self as *mut Term).write(Term::Max(ts));
                    },
                    Term::Min(ts) => unsafe {
                        for t in ts.iter_mut() {
                            let tp = t as *mut Term;
                            tp.write(Term::Add(tp.read().into(), *l));
                            t.fold_add();
                        }
                        let ts = std::mem::take(ts);
                        drop_as_manually_drop(tp.read());
                        (self as *mut Term).write(Term::Min(ts));
                    },
                }
            },
            Term::Max(ts) | Term::Min(ts) => {
                for t in ts.iter_mut() {
                    t.fold_add();
                }
            },
        }
    }

    fn distribute_max_min(&mut self) {
        match self {
            Term::Var(..) => (),
            Term::Add(t, _) => {
                t.distribute_max_min();
            },
            Term::Max(ts) => {
                if matches!(ts.last(), Some(Term::Min(_))) {
                    if let Some(Term::Min(ts2)) = ts.pop() {
                        let mut new_ts = Vec::with_capacity(ts.len() * ts2.len());

                        for t in ts2 {
                            let mut ts = ts.clone();
                            ts.push(t);
                            new_ts.push(Term::Max(ts));
                        }

                        *ts = new_ts;
                    } else {
                        unreachable!()
                    }
                }
                
                for t in ts {
                    t.distribute_max_min();
                }
            },
            Term::Min(ts) => for t in ts {
                t.distribute_max_min();
            },
        }
    }

    fn fold_max_min(&mut self) {
        match self {
            Term::Var(..) => (),
            Term::Add(t, _) => {
                t.fold_max_min();
            },
            Term::Max(ts) => {
                if let Some((mid, _)) = ts
                    .iter()
                    .enumerate()
                    .find(|(_, t)| matches!(t, Term::Max(_)))
                {
                    let end = ts
                        .iter()
                        .enumerate()
                        .skip(mid)
                        .find(|(_, t)| !matches!(t, Term::Max(_)))
                        .map(|(i, _)| i)
                        .unwrap_or(ts.len());
                    let mut drain = ts.drain(mid..end);
                    let mut first = if let Some(Term::Max(first)) = drain.next() {
                        first
                    } else {
                        unreachable!()
                    };
                    while let Some(Term::Max(ts)) = drain.next() {
                        first.extend(ts);
                    }
                    for t in first.iter_mut() {
                        t.fold_max_min();
                    }
                    std::mem::drop(drain);
                    ts.extend(first);
                }
            },
            Term::Min(ts) => {
                if let Some((mid, _)) = ts
                    .iter()
                    .enumerate()
                    .find(|(_, t)| matches!(t, Term::Min(_)))
                {
                    let mut drain = ts.drain(mid + 1..);
                    let mut first = if let Some(Term::Min(first)) = drain.next() {
                        first
                    } else {
                        unreachable!()
                    };
                    while let Some(Term::Min(ts)) = drain.next() {
                        first.extend(ts);
                    }
                    for t in first.iter_mut() {
                        t.fold_max_min();
                    }
                    std::mem::drop(drain);
                    ts.extend(first);
                }
            },
        }
    }

    fn normalize(&mut self) {
        self.fold_add(); // now all adds are attached directly to variables
        self.desingleton_max_min(); // turn all singleton min/max to their element
        self.sort_max_min(); // sort and dedup (only those not under Add, which none are)
        self.fold_max_min(); // combine all min/max
        self.distribute_max_min(); // distribute min/max so that we have minimum of maximums
        self.sort_max_min(); // sort and dedup (only those not under Add, which none are)
        self.fold_max_min(); // combine all min/max
        self.sort_max_min(); // sort and dedup (only those not under Add, which none are)
    }

    fn into_max(self) -> MResult<Box<[(Var, Level)]>> {
        Ok(match self {
            Term::Var(_, v) => Box::new([(v, 0.into())]),
            Term::Add(t, l) => match *t {
                Term::Var(_, v) => Box::new([(v, l)]),
                t => bail!(
                    "when compiling max constraint, had Term::Add([not var: {:?}], {:?})",
                    t,
                    l,
                ),
            },
            Term::Max(ts) => {
                let mut new = Vec::with_capacity(ts.len());

                for t in ts {
                    new.push(match t {
                        Term::Var(_, v) => (v, 0.into()),
                        Term::Add(t, l) => match *t {
                            Term::Var(_, v) => (v, l),
                            t => bail!(
                                "when compiling max constraint, had Term::Max with \
                                 Term::Add([not var: {:?}], {:?})",
                                t,
                                l,
                            ),
                        },
                        t => bail!("when max compiling constraint, had Term::Max with {:#?}", t),
                    });
                }

                new.into_boxed_slice()
            },
            Term::Min(ts) => bail!("when max compiling constraint, had Term::Min({:#?})", ts),
        })
    }

    fn into_min(self) -> MResult<Box<[(Var, Level)]>> {
        Ok(match self {
            Term::Var(_, v) => Box::new([(v, 0.into())]),
            Term::Add(t, l) => match *t {
                Term::Var(_, v) => Box::new([(v, l)]),
                t => bail!(
                    "when compiling min constraint, had Term::Add([not var: {:?}], {:?})",
                    t,
                    l,
                ),
            },
            Term::Max(ts) => bail!("when min compiling constraint, had Term::Max({:#?})", ts),
            Term::Min(ts) => {
                let mut new = Vec::with_capacity(ts.len());

                for t in ts {
                    new.push(match t {
                        Term::Var(_, v) => (v, 0.into()),
                        Term::Add(t, l) => match *t {
                            Term::Var(_, v) => (v, l),
                            t => bail!(
                                "when compiling min constraint, had Term::Min with \
                                 Term::Add([not var: {:?}], {:?})",
                                t,
                                l,
                            ),
                        },
                        t => bail!("when min compiling constraint, had Term::Min with {:#?}", t),
                    });
                }

                new.into_boxed_slice()
            },
        })
    }

    pub fn shift(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        match self {
            Term::Var(db, _) => if *db >= cutoff {
                if by.is_negative() {
                    *db -= by.unsigned_abs();
                } else {
                    *db += by.unsigned_abs();
                } 
            },
            Term::Add(t, _) => {
                t.shift(by, cutoff);
            },
            Term::Max(ts) | Term::Min(ts) => {
                for t in ts {
                    t.shift(by, cutoff);
                }
            },
        }
    }

    pub fn subst(&mut self, db: DeBruijn, new: &Term) {
        match self {
            &mut Term::Var(d, _) => if d == db {
                self.clone_from(new);
            },
            Term::Add(t, _) => {
                t.subst(db, new);
            },
            Term::Max(ts) | Term::Min(ts) => {
                for t in ts {
                    t.subst(db, new);
                }
            },
        }
    }
}

impl AddAssign<Level> for Term {
    fn add_assign(&mut self, rhs: Level) {
        *self = Term::Add(std::mem::replace(self, Term::Var(0, Var(0))).into(), rhs);
    }
}

impl SubAssign<Level> for Term {
    fn sub_assign(&mut self, rhs: Level) {
        *self += -rhs;
    }
}

impl Add<Level> for Term {
    type Output = Self;

    fn add(mut self, rhs: Level) -> Self::Output {
        self += rhs;
        self
    }
}

impl Sub<Level> for Term {
    type Output = Self;

    fn sub(mut self, rhs: Level) -> Self::Output {
        self -= rhs;
        self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintType {
    Gt,
    Ge,
    Le,
    Lt,
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub left: Term,
    pub c: ConstraintType,
    pub right: Term,
}

impl Constraint {
    fn compile(mut self) -> MResult<CompiledConstraints> {
        self.left.normalize();
        self.right.normalize();
        if self.c == ConstraintType::Gt || self.c == ConstraintType::Ge {
            std::mem::swap(&mut self.left, &mut self.right);
        }
        Ok(CompiledConstraints {
            lesser_max: self.left.into_max()?,
            refl: self.c == ConstraintType::Ge || self.c == ConstraintType::Le,
            greater_min: self.right.into_min()?,
        })
    }
}

#[derive(Debug, Clone)]
struct CompiledConstraints {
    pub lesser_max: Box<[(Var, Level)]>,
    pub refl: bool,
    pub greater_min: Box<[(Var, Level)]>,
}

impl CompiledConstraints {
    fn into_constraints(self) -> Vec<CompiledConstraint> {
        let mut constraints = Vec::with_capacity(self.lesser_max.len() * self.greater_min.len());

        for &(lesser_var, lesser_offset) in self.lesser_max.iter() {
            for &(greater_var, greater_offset) in self.greater_min.iter() {
                constraints.push(CompiledConstraint {
                    lesser_var,
                    lesser_offset,
                    refl: self.refl,
                    greater_var,
                    greater_offset,
                });
            }
        }

        constraints
    }
}

#[derive(Debug, Clone)]
struct CompiledConstraint {
    pub lesser_var: Var,
    pub lesser_offset: Level,
    pub refl: bool,
    pub greater_var: Var,
    pub greater_offset: Level,
}

impl CompiledConstraint {
    fn edge_weight(&self) -> Level {
        let mut weight = self.greater_offset - self.lesser_offset;
        if !self.refl {
            weight -= 1;
        }
        weight
    }
}

#[derive(Debug, Clone, Copy)]
enum NodeData {
    Zero,
    Omega2,
    Var(u32),
}

impl Display for NodeData {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            NodeData::Zero => f.write_str("0"),
            NodeData::Omega2 => f.write_str("2ω"),
            &NodeData::Var(v) => write!(f, "Var #{}", v - 2),
        }
    }
}

#[derive(Debug, Clone)]
pub struct UniChecker {
    zero: NodeIndex<u32>,
    omega2: NodeIndex<u32>,
    graph: DiGraph<NodeData, Level, u32>,
}

impl UniChecker {
    pub fn fresh_var(&mut self) -> Var {
        let node = self.graph.add_node(NodeData::Var(self.graph.node_count() as u32));
        self.graph.add_edge(node, self.zero, 0.into());
        self.graph.add_edge(self.omega2, node, (-1).into());
        node.into()
    }

    pub fn clone_var(&mut self, var: Var) -> Var {
        let old = var.into();
        let new = self.graph.add_node(NodeData::Var(self.graph.node_count() as u32));
        let mut in_walker = self.graph.neighbors_directed(old, Direction::Incoming).detach();
        let mut out_walker = self.graph.neighbors_directed(old, Direction::Outgoing).detach();

        while let Some((e, neighbor)) = in_walker.next(&self.graph) {
            self.graph.add_edge(neighbor, new, self.graph[e].clone());
        }

        while let Some((e, neighbor)) = out_walker.next(&self.graph) {
            self.graph.add_edge(new, neighbor, self.graph[e].clone());
        }

        new.into()
    }

    pub fn zero(&self) -> Var {
        self.zero.into()
    }

    pub fn insert_constraint(&mut self, c: Constraint) -> MResult<()> {
        for c in c.compile()?.into_constraints() {
            let weight = c.edge_weight();
            if let Some(edge) = self.graph.find_edge(c.greater_var.into(), c.lesser_var.into()) {
                if weight < self.graph[edge] {
                    self.graph[edge] = weight;
                }
            } else {
                self.graph.add_edge(c.greater_var.into(), c.lesser_var.into(), weight);
            }
        }

        Ok(())
    }

    pub fn try_extend(&mut self, iter: impl IntoIterator<Item=Constraint>) -> MResult<()> {
        for c in iter {
            self.insert_constraint(c)?;
        }

        Ok(())
    }

    pub fn is_consistent(&self) -> Result<(), Vec<NodeIndex<u32>>> {
        if let Some(cycle) = find_negative_cycle(&self.graph, self.zero) {
            Err(cycle)
        } else {
            Ok(())
        }
    }

    pub fn create_dot_report(&self, cycle: &Vec<NodeIndex<u32>>) -> String {
        Dot::with_attr_getters(
            &self.graph,
            &[],
            &move |_, e| {
                let red = match cycle.iter().enumerate().find(|&(_, &n)| n == e.source()) {
                    Some((i, _)) if i == cycle.len() - 1 => cycle[0] == e.target(),
                    Some((i, _)) => cycle[i + 1] == e.target(),
                    None => false,
                };
                if red {
                    ", color = red, style = \"bold\"".to_string()
                } else if e.target() == self.omega2
                    || (e.target() == self.zero && *e.weight() == 0.into())
                    || (e.source() == self.omega2
                        && (e.target() == self.zero || *e.weight() == (-1).into()))
                {
                    ", color = \"#0000003F\", style = \"dashed\""
                        .to_string()
                } else {
                    String::new()
                }
            },
            &move |_, (n, _)| if cycle.contains(&n) {
                ", color = red, style = \"bold\"".to_string()
            } else if n == self.zero || n == self.omega2 {
                ", color = \"#0000001F\", fontcolor = \"#0000001F\"".to_string()
            } else {
                String::new()
            },
        ).to_string()
    }
}

impl Default for UniChecker {
    fn default() -> Self {
        let mut graph = DiGraph::with_capacity(10000, 1000);
        let zero = graph.add_node(NodeData::Zero);
        let omega2 = graph.add_node(NodeData::Omega2);
        graph.add_edge(zero, omega2, Level::new(2, 0));
        graph.add_edge(omega2, zero, -Level::new(2, 0));
        UniChecker { zero, omega2, graph }
    }
}

unsafe fn drop_as_manually_drop<T>(t: Box<T>) {
    use std::mem::*;
    drop::<Box<ManuallyDrop<T>>>(transmute(t))
}

// Replace the new `old` with the contents of `new` and drop `new`.
//
// The data in `old` will simply be overwritten as opposed to dropped.
//
// # Safety
//
// After calling this function, the data referenced by `new` must never be
// accessed, and the `Box` be considered invalid.
unsafe fn replace_new_and_drop<T>(old: *mut Box<T>, new: *mut Box<T>) {
    let mut old_box = old.read();
    let old_p = old_box.as_mut() as *mut T;
    let mut new_box = new.read();
    let new_p = new_box.as_mut() as *const T;
    old_p.write(new_p.read());
    std::mem::forget(old_box);
    drop_as_manually_drop(new_box);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_normalization() {
        let mut checker = UniChecker::default();
        let v1 = Term::Var(0, checker.fresh_var());
        let v2 = Term::Var(0, checker.fresh_var());
        let v3 = Term::Var(0, checker.fresh_var());
        let v4 = Term::Var(0, checker.fresh_var());
        let v5 = Term::Var(0, checker.fresh_var());
        let mut t = Term::Max(vec![
            Term::Max(vec![
                Term::Min(vec![
                    v1.clone() + 200.into(),
                    v2.clone(),
                    Term::Min(vec![v3.clone()]),
                ]),
            ]) - 9.into(),
            v4.clone(),
            v4.clone(),
            v5.clone() + Level::new(69, 0),
        ]) + 5.into();
        t.normalize();
        assert_eq!(t, Term::Max(vec![
            v1 + 196.into(),
            v2 - 4.into(),
            v3 - 4.into(),
            v4 + 5.into(),
            v5 + Level::new(69, 5),
        ]));
    }

    #[test]
    fn sat_graph() {
        let mut checker = UniChecker::default();
        let v1 = Term::Var(0, checker.fresh_var());
        let v2 = Term::Var(0, checker.fresh_var());
        let v3 = Term::Var(0, checker.fresh_var());
        let v4 = Term::Var(0, checker.fresh_var());
        checker.try_extend([
            Constraint {
                left: v1.clone(),
                c: ConstraintType::Le,
                right: v4.clone() + 1.into(),
            },
            Constraint {
                left: v2.clone(),
                c: ConstraintType::Le,
                right: v1.clone() + 2.into(),
            },
            Constraint {
                left: v2.clone(),
                c: ConstraintType::Le,
                right: v4.clone(),
            },
            Constraint {
                left: v3.clone(),
                c: ConstraintType::Le,
                right: v1.clone() + 1.into(),
            },
            Constraint {
                left: v4.clone(),
                c: ConstraintType::Le,
                right: v1.clone() - 1.into(),
            },
            Constraint {
                left: v4.clone(),
                c: ConstraintType::Le,
                right: v3.clone() - 2.into(),
            },
        ]).unwrap();
        assert!(checker.is_consistent().is_ok());
    }

    #[test]
    fn unsat_graph() {
        let mut checker = UniChecker::default();
        let v1 = Term::Var(0, checker.fresh_var());
        let v2 = Term::Var(0, checker.fresh_var());
        let v3 = Term::Var(0, checker.fresh_var());
        let v4 = Term::Var(0, checker.fresh_var());
        checker.try_extend([
            Constraint {
                left: v1.clone(),
                c: ConstraintType::Le,
                right: v4.clone() + 1.into(),
            },
            Constraint {
                left: v2.clone(),
                c: ConstraintType::Le,
                right: v1.clone() + 2.into(),
            },
            Constraint {
                left: v2.clone(),
                c: ConstraintType::Le,
                right: v4.clone(),
            },
            Constraint {
                left: v3.clone(),
                c: ConstraintType::Le,
                right: v1.clone() + 1.into(),
            },
            Constraint {
                left: v4.clone(),
                c: ConstraintType::Le,
                right: v1.clone() - 1.into(),
            },
            Constraint {
                left: v4.clone(),
                c: ConstraintType::Le,
                right: v3.clone() - 2.into(),
            },
            Constraint {
                left: v4.clone(),
                c: ConstraintType::Lt,
                right: v3.clone() - 2.into(),
            },
        ]).unwrap();
        eprintln!("{}", checker.create_dot_report(&checker.is_consistent().unwrap_err()));
        assert!(checker.is_consistent().is_err());
    }
}

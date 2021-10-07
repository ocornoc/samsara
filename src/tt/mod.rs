pub use univ::{*, Term as Univ};

pub type DeBruijn = u32;
pub type SDeBruijn = i32;

pub mod univ;

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Sort(Univ),
    Level,
    Bound(DeBruijn),
    Lam(Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
    Pi(Box<Term>, Box<Term>),
    IRCode(Box<Term>),
    IRElement(Box<Term>),
    IRChoose(Box<Term>, Box<Term>),
    IRRecurse(Box<Term>, Box<Term>),
    Constr(Box<Term>),
}

impl Term {
    fn is_sort(&self) -> bool {
        matches!(self, Term::Sort(_))
    }

    pub fn shift(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        match self {
            Term::Bound(b) if *b >= cutoff => if by.is_negative() {
                *b -= by.unsigned_abs();
            } else {
                *b += by.unsigned_abs();
            },
            Term::Bound(_) | Term::Level => (),
            Term::Sort(b) => {
                b.shift(by, cutoff);
            },
            Term::Lam(f, s) | Term::Pi(f, s) | Term::IRChoose(f, s) | Term::IRRecurse(f, s) => {
                f.shift(by, cutoff);
                s.shift(by, cutoff + 1);
            },
            Term::App(l, r) => {
                l.shift(by, cutoff);
                r.shift(by, cutoff);
            },
            Term::IRCode(e) | Term::IRElement(e) | Term::Constr(e) => {
                e.shift(by, cutoff);
            },
        }
    }

    pub fn subst(&mut self, db: DeBruijn, t: &Term) {
        match self {
            &mut Term::Bound(b) if b == db => {
                self.clone_from(t);
            },
            Term::Bound(_) | Term::Level => (),
            Term::Sort(b) => if let Term::Sort(t) = t {
                b.subst(db, t)
            },
            Term::Lam(f, s) | Term::Pi(f, s) | Term::IRChoose(f, s) | Term::IRRecurse(f, s) => {
                f.subst(db, t);
                s.subst(db + 1, t);
            },
            Term::App(l, r) => {
                l.subst(db, t);
                r.subst(db, t);
            },
            Term::IRCode(e) | Term::IRElement(e) | Term::Constr(e) => {
                e.subst(db, t);
            },
        }
    }

    pub fn normalize_mut(&mut self) {
        match self {
            Term::Sort(_) | Term::Bound(_) | Term::Level => (),
            Term::Lam(ty, e) | Term::Pi(ty, e) => {
                ty.normalize_mut();
                e.normalize_mut();
            },
            Term::App(l, r) => {
                l.normalize_mut();
                if let Term::Lam(_, e) = l.as_mut() {
                    e.subst(0, r);
                    e.shift(-1, 1);
                    e.normalize_mut();
                    *self = e.as_ref().clone();
                } else if let Term::Constr(code) = l.as_mut() {
                    match code.as_mut() {
                        Term::IRElement(d) => {
                            *self = Term::App(r.clone(), d.clone());
                            self.normalize_mut();
                        },
                        Term::IRChoose(a, u) => {
                            let mut u = u.clone();
                            u.shift(1, 0);
                            let mut r = r.clone();
                            r.shift(1, 0);
                            let mut left = Term::App(u, Term::Bound(0).into());
                            left = Term::Constr(left.into());
                            left = Term::App(left.into(), r.clone()).normalize();
                            *self = Term::Pi(a.clone(), left.into());
                        },
                        Term::IRRecurse(i, v) => {
                            let mut v = v.clone();
                            v.shift(2, 0);
                            let mut r = r.clone();
                            r.shift(2, 0);
                            let mut i1 = i.clone();
                            i1.shift(1, 0);
                            let mut term = Term::Constr(Term::App(v, Term::Bound(1).into()).into());
                            term = Term::App(term.into(), r.clone()).normalize();
                            term = Term::Pi(
                                Term::Pi(i1, Term::App(r, Term::App(
                                    Term::Bound(1).into(),
                                    Term::Bound(0).into(),
                                ).into()).normalize().into()).into(),
                                term.into(),
                            );
                            *self = Term::Pi(
                                Term::Pi(i.clone(), todo!()).into(),
                                term.into(),
                            );
                        },
                        _ => {
                            r.normalize_mut();
                        },
                    }
                } else {
                    r.normalize_mut();
                }
            },
            Term::IRCode(_) => todo!(),
            Term::IRElement(_) => todo!(),
            Term::IRChoose(_, _) => todo!(),
            Term::IRRecurse(_, _) => todo!(),
            Term::Constr(_) => todo!(),
        }
    }

    pub fn normalize(mut self) -> Self {
        self.normalize_mut();
        self
    }
}

#[derive(Debug, Clone)]
pub struct Context(pub Vec<Term>);

impl Context {
    pub fn infer_ty(&mut self, t: &Term) -> Option<Term> {
        match t {
            Term::Sort(_) => Some(t.clone()), // FIXME: atm only one universe level
            &Term::Bound(db) => self.0.get(db as usize).cloned(),
            Term::Lam(ty, e) => {
                if !self.infer_ty(ty)?.normalize().is_sort() {
                    return None;
                }
                self.0.push(ty.as_ref().clone());
                let e = self.infer_ty(e);
                self.0.pop();
                e
            },
            Term::App(l, r) => match self.infer_ty(l)?.normalize() {
                Term::Pi(ll, lr) => {
                    let rty = self.infer_ty(r)?.normalize();
                    if *ll == rty {
                        Some(*lr)
                    } else {
                        None
                    }
                },
                _ => None,
            },
            Term::Pi(ty, e) => {
                let _ty_sort = match self.infer_ty(ty)?.normalize() {
                    Term::Sort(u) => u,
                    _ => return None,
                };
                self.0.push(ty.as_ref().clone());
                let e = self.infer_ty(e);
                self.0.pop();
                match self.infer_ty(&e?)?.normalize() {
                    Term::Sort(e_sort) => Some(Term::Sort(e_sort)), // FIXME: no universe checking
                    _ => None,
                }
            },
            Term::IRCode(_) => todo!(),
            Term::IRElement(_) => todo!(),
            Term::IRChoose(_, _) => todo!(),
            Term::IRRecurse(_, _) => todo!(),
            Term::Constr(_) => todo!(),
            Term::Level => todo!(),
        }
    }
}
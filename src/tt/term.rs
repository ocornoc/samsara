use std::cell::RefCell;
use miette::{miette, ensure, bail, Result as MResult, Error as Report};
use lazy_static::lazy_static;
use parking_lot::Mutex;
use super::*;

lazy_static! {
    pub static ref CONSTRAINT_CHECKER: Mutex<UniChecker> = Default::default();
    pub static ref BOOL_TYPE: Var = CONSTRAINT_CHECKER.lock().fresh_var();
    pub static ref UNIT_TYPE: Var = CONSTRAINT_CHECKER.lock().fresh_var();
}

pub type DeBruijn = u32;
pub type SDeBruijn = i32;

macro_rules! term_ctor {
    ($ctorname:ident, $name:tt $( ,)? $($arg:ident),*) => {
        pub fn $ctorname(self, $($arg: Term),*) -> Term {
            Term::$name(self.into(), $(Box::new($arg)),*)
        }
    };
}

#[derive(Debug, Clone)]
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
    Constr(RefCell<Option<Box<Term>>>, Box<Term>),
    Bool,
    Tt,
    Ff,
    Ite(Box<Term>),
    Unit,
    Star,
}

impl Term {
    term_ctor!(lam, Lam, body);
    term_ctor!(app, App, r);
    term_ctor!(pi, Pi, body);
    term_ctor!(ir_code, IRCode);
    term_ctor!(ir_elem, IRElement);
    term_ctor!(ir_choose, IRChoose, f);
    term_ctor!(ir_recurse, IRRecurse, r);
    term_ctor!(ite, Ite);

    pub fn constr(self) -> Self {
        Term::Constr(None.into(), self.into())
    }

    pub fn shift(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        match self {
            Term::Bound(b) if *b >= cutoff => if by.is_negative() {
                *b -= by.unsigned_abs();
            } else {
                *b += by.unsigned_abs();
            },
            Term::Bound(_) | Term::Level | Term::Bool | Term::Tt | Term::Ff | Term::Unit
            | Term::Star => (),
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
            Term::IRCode(e) | Term::IRElement(e) | Term::Ite(e) => {
                e.shift(by, cutoff);
            },
            Term::Constr(ty, e) => {
                e.shift(by, cutoff);
                if let Some(ty) = ty.borrow_mut().as_mut() {
                    ty.shift(by, cutoff);
                }
            },
        }
    }

    fn ite_applied_mut(&mut self) -> Option<(&mut Term, &mut Term, &mut Term)> {
        if let Term::App(l, r) = self {
            if let Term::App(ll, lr) = l.as_mut() {
                if let Term::App(lll, llr) = ll.as_mut() {
                    if let Term::Ite(ty) = lll.as_mut() {
                        return Some((ty, lr, r));
                    }
                }
            }
        }
        None
    }

    pub fn subst(&mut self, db: DeBruijn, t: &Term) {
        match self {
            &mut Term::Bound(b) if b == db => {
                self.clone_from(t);
            },
            Term::Bound(_) | Term::Level | Term::Bool | Term::Tt | Term::Ff | Term::Unit
            | Term::Star => (),
            Term::Sort(b) => if let Term::Sort(t) = t {
                b.subst(db, t, &mut CONSTRAINT_CHECKER.lock())
            },
            Term::Lam(f, s) | Term::Pi(f, s) | Term::IRChoose(f, s) | Term::IRRecurse(f, s) => {
                f.subst(db, t);
                s.subst(db + 1, t);
            },
            Term::App(l, r) => {
                l.subst(db, t);
                r.subst(db, t);
            },
            Term::IRCode(e) | Term::IRElement(e) | Term::Ite(e) => {
                e.subst(db, t);
            },
            Term::Constr(ty, e) => {
                e.subst(db, t);
                if let Some(ty) = ty.borrow_mut().as_mut() {
                    ty.subst(db, t);
                }
            },
        }
    }

    pub fn normalize_mut(&mut self) {
        match self {
            Term::Sort(_) | Term::Bound(_) | Term::Level | Term::Bool | Term::Tt | Term::Ff
            | Term::Unit | Term::Star => (),
            Term::Lam(ty, e) | Term::Pi(ty, e) => {
                ty.normalize_mut();
                e.normalize_mut();
            },
            Term::App(l, r) => {
                l.normalize_mut();
                match l.as_mut() {
                    Term::Lam(ty, e) => {
                        if matches!(**ty, Term::Level) {
                            r.normalize_mut();
                        }
                        e.subst(0, r);
                        e.shift(-1, 1);
                        e.normalize_mut();
                        *self = e.as_ref().clone();
                    },
                    Term::Constr(ty, code) => {
                        code.normalize_mut();
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
                                let mut left = u.app(Term::Bound(0)).normalize();
                                left = Term::Constr(ty.clone(), left.into());
                                *self = a.clone().pi(left.app(r.as_ref().clone())).normalize();
                            },
                            Term::IRRecurse(i, v) => {
                                let mut v = v.clone();
                                v.shift(2, 0);
                                let mut r = r.clone();
                                r.shift(2, 0);
                                let mut i1 = i.clone();
                                i1.shift(1, 0);
                                let mut term = Term::Constr(
                                    ty.clone(),
                                    v.app(Term::Bound(1)).into(),
                                ).app(r.as_ref().clone());
                                term = i1
                                    .pi(r.app(Term::Bound(1).app(Term::Bound(0))))
                                    .pi(term);
                                let ty = ty.get_mut().as_mut().unwrap().clone();
                                *self = i.clone().pi(*ty).pi(term).normalize();
                            },
                            _ => match code.ite_applied_mut() {
                                Some((c@Term::IRCode(_), llr, lr)) => {
                                    *llr = Term::Constr(
                                        ty.clone(),
                                        std::mem::replace(llr, Term::Bool).into(),
                                    ).app(r.as_ref().clone()).normalize();
                                    *lr = Term::Constr(
                                        ty.clone(),
                                        std::mem::replace(lr, Term::Bool).into(),
                                    ).app(r.as_ref().clone()).normalize();
                                    *c = CONSTRAINT_CHECKER.lock().fresh_var().into();
                                    *self = std::mem::replace(code.as_mut(), Term::Bool);
                                },
                                _ => {
                                    r.normalize_mut();
                                },
                            },
                        }
                    },
                    Term::App(ll, lr) => {
                        if let Term::App(lll, llr) = ll.as_mut() {
                            if matches!(**lll, Term::Ite(_)) {
                                match llr.as_mut() {
                                    Term::Tt => {
                                        *self = lr.as_ref().clone();
                                        return;
                                    },
                                    Term::Ff => {
                                        *self = r.as_ref().clone();
                                        return;
                                    },
                                    _ => (),
                                }
                            }
                        }
                        r.normalize_mut();
                    },
                    _ => {
                        r.normalize_mut();
                    },
                }
            },
            Term::IRCode(t) | Term::IRElement(t) => {
                t.normalize_mut()
            },
            Term::IRChoose(f, s) | Term::IRRecurse(f, s) => {
                f.normalize_mut();
                s.normalize_mut();
            },
            Term::Constr(f, s) => {
                if let Some(f) = f.get_mut() {
                    f.normalize_mut();
                }
                s.normalize_mut();
            },
            Term::Ite(ty) => {
                ty.normalize_mut();
            },
        }
    }

    pub fn normalize(mut self) -> Self {
        self.normalize_mut();
        self
    }

    fn into_pi(self) -> Result<(Term, Term), Term> {
        if let Term::Pi(ty, e) = self {
            Ok((*ty, *e))
        } else {
            Err(self)
        }
    }

    fn into_sort(self) -> Result<Univ, Term> {
        if let Term::Sort(u) = self {
            Ok(u)
        } else {
            Err(self)
        }
    }
}

impl From<Univ> for Term {
    #[inline]
    fn from(u: Univ) -> Self {
        Term::Sort(u)
    }
}

impl From<Var> for Term {
    #[inline]
    fn from(v: Var) -> Self {
        Term::Sort(v.into())
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Sort(l0), Self::Sort(r0)) => {
                let mut checker = CONSTRAINT_CHECKER.lock();
                let mut c = Constraint {
                    left: l0.clone(),
                    c: ConstraintType::Le,
                    right: r0.clone(),
                };
                checker.insert_constraint(c.clone()).unwrap();
                c.c = ConstraintType::Ge;
                checker.insert_constraint(c).unwrap();
                true
            },
            (Self::Bound(l0), Self::Bound(r0)) => l0 == r0,
            (Self::Lam(l0, l1), Self::Lam(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::App(l0, l1), Self::App(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::Pi(l0, l1), Self::Pi(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::IRCode(l0), Self::IRCode(r0)) => l0 == r0,
            (Self::IRElement(l0), Self::IRElement(r0)) => l0 == r0,
            (Self::IRChoose(l0, l1), Self::IRChoose(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::IRRecurse(l0, l1), Self::IRRecurse(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::Constr(_, l), Self::Constr(_, r)) => l == r,
            (Self::Ite(l0), Self::Ite(r0)) => l0 == r0,
            _ => std::mem::discriminant(self) == std::mem::discriminant(other),
        }
    }
}

impl Eq for Term {}

impl PartialOrd for Term {
    fn lt(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Sort(l0), Self::Sort(r0)) => {
                let mut checker = CONSTRAINT_CHECKER.lock();
                checker.insert_constraint(Constraint {
                    left: l0.clone(),
                    c: ConstraintType::Lt,
                    right: r0.clone(),
                }).unwrap();
                true
            },
            (Self::Bound(l0), Self::Bound(r0)) => l0 < r0,
            (Self::Lam(l0, l1), Self::Lam(r0, r1)) => l0 > r0 && l1 < r1,
            (Self::App(l0, l1), Self::App(r0, r1)) => l0 < r0 && l1 < r1,
            (Self::Pi(l0, l1), Self::Pi(r0, r1)) => l0 > r0 && l1 < r1,
            (Self::IRCode(l0), Self::IRCode(r0)) => l0 < r0,
            (Self::IRElement(l0), Self::IRElement(r0)) => l0 < r0,
            (Self::IRChoose(l0, l1), Self::IRChoose(r0, r1)) => l0 < r0 && l1 < r1,
            (Self::IRRecurse(l0, l1), Self::IRRecurse(r0, r1)) => l0 < r0 && l1 < r1,
            (Self::Constr(_, l), Self::Constr(_, r)) => l < r,
            (Self::Ite(l0), Self::Ite(r0)) => l0 < r0,
            _ => false,
        }
    }

    fn le(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Sort(l0), Self::Sort(r0)) => {
                let mut checker = CONSTRAINT_CHECKER.lock();
                checker.insert_constraint(Constraint {
                    left: l0.clone(),
                    c: ConstraintType::Le,
                    right: r0.clone(),
                }).unwrap();
                true
            },
            (Self::Bound(l0), Self::Bound(r0)) => l0 <= r0,
            (Self::Lam(l0, l1), Self::Lam(r0, r1)) => l0 >= r0 && l1 <= r1,
            (Self::App(l0, l1), Self::App(r0, r1)) => l0 <= r0 && l1 <= r1,
            (Self::Pi(l0, l1), Self::Pi(r0, r1)) => l0 >= r0 && l1 <= r1,
            (Self::IRCode(l0), Self::IRCode(r0)) => l0 <= r0,
            (Self::IRElement(l0), Self::IRElement(r0)) => l0 <= r0,
            (Self::IRChoose(l0, l1), Self::IRChoose(r0, r1)) => l0 <= r0 && l1 <= r1,
            (Self::IRRecurse(l0, l1), Self::IRRecurse(r0, r1)) => l0 <= r0 && l1 <= r1,
            (Self::Constr(l0, l1), Self::Constr(r0, r1)) => l0 <= r0 && l1 <= r1,
            (Self::Ite(l0), Self::Ite(r0)) => l0 <= r0,
            _ => std::mem::discriminant(self) == std::mem::discriminant(other),
        }
    }

    fn gt(&self, other: &Self) -> bool {
        other.lt(self)
    }

    fn ge(&self, other: &Self) -> bool {
        other.le(self)
    }

    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        unimplemented!()
    }
}

#[derive(Debug, Clone, Default)]
pub struct Context(pub Vec<Term>);

impl Context {
    #[cold]
    #[inline(never)]
    fn db_index_failed(&self, db: u32) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn lam_arg_ty_not_sort(&self, ty: &Term, tyty: &Term, e: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn app_l_not_pi(&self, l: &Term, lty: &Term, r: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn app_arg_ty_not_ll(&self, l: &Term, r: &Term, ll: &Term, lr: &Term, rty: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn pi_arg_ty_not_sort(&self, ty: &Term, tyty: &Term, ety: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn pi_e_ty_not_sort(&self, ty: &Term, tyty: &Univ, e: &Term, ety: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_code_not_sort(&self, t: &Term, ty: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_choose_a_not_sort(&self, a: &Term, aty: &Term, f: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_choose_fty_not_pi(&self, a: &Term, a_sort: &Univ, f: &Term, fty: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_choose_pty_not_a(
        &self,
        a: &Term,
        aty: &Univ,
        f: &Term,
        pty: &Term,
        out: &Term,
    ) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_choose_outty_not_sort(
        &self,
        a: &Term,
        aty: &Univ,
        f: &Term,
        pty: &Term,
        out: &Term,
        outty: &Term,
    ) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_choose_f_out_not_ir_code(
        &self,
        a: &Term,
        aty: &Univ,
        f: &Term,
        pty: &Term,
        out: &Term,
    ) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_rec_i_not_sort(&self, i: &Term, ity: &Term, r: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_rec_rty_not_pi(&self, i: &Term, i_sort: &Univ, r: &Term, rty: &Term) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_rec_pty_not_pi(
        &self,
        i: &Term,
        i_sort: &Univ,
        r: &Term,
        pty: &Term,
        out: &Term,
    ) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_rec_ppty_not_i(
        &self,
        t: &Term,
        i: &Term,
        ppty: &Term,
    ) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_rec_out_not_code(
        &self,
        t: &Term,
        out: &Term,
    ) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_rec_pout_not_out(
        &self,
        t: &Term,
        out: &Term,
        pout: &Term,
    ) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_rec_out_ty_not_sort(
        &self,
        t: &Term,
        out: &Term,
        outty: &Term,
    ) -> Report {
        todo!()
    }

    #[cold]
    #[inline(never)]
    fn ir_constr_codety_not_code(
        &self,
        t: &Term,
        code: &Term,
        codety: &Term,
    ) -> Report {
        todo!()
    }

    pub fn infer_ty(&mut self, t: &Term) -> MResult<Term> {
        match t {
            Term::Sort(t) => {
                let mut checker = CONSTRAINT_CHECKER.lock();
                let v = checker.fresh_var();
                checker.insert_constraint(Constraint {
                    left: t.clone(),
                    c: ConstraintType::Lt,
                    right: v.into(),
                })?;
                Ok(v.into())
            },
            &Term::Bound(db) => self.0.get(self.0.len() - db as usize - 1).cloned().ok_or_else(||
                self.db_index_failed(db)
            ),
            Term::Level => Ok(Term::Sort(Univ::Var(None, {
                let mut checker = CONSTRAINT_CHECKER.lock();
                let v = checker.fresh_var();
                let zero = checker.zero();
                checker.insert_constraint(Constraint {
                    left: Univ::Var(None, zero) + Level::new(1, 0),
                    c: ConstraintType::Le,
                    right: v.into(),
                })?;
                v
            }))),
            Term::Lam(ty, e) => {
                let tyty = self.infer_ty(ty)?.normalize();
                if !matches!(tyty, Term::Sort(_)) {
                    return Err(self.lam_arg_ty_not_sort(ty, &tyty, e));
                }
                self.0.push(ty.as_ref().clone());
                let e = self.infer_ty(e)?;
                self.0.pop();
                Ok(ty.clone().pi(e))
            },
            Term::App(l, r) => match self.infer_ty(l)?.normalize() {
                Term::Pi(ll, lr) => {
                    let rty = self.infer_ty(r)?.normalize();
                    if *ll >= rty {
                        Ok(*lr)
                    } else {
                        Err(self.app_arg_ty_not_ll(l, r, &ll, &lr, &rty))
                    }
                },
                lty => Err(self.app_l_not_pi(l, &lty, r)),
            },
            Term::Pi(ty, e) => {
                let ty_sort = self.infer_ty(ty)?.normalize().into_sort().map_err(|tyty| {
                    self.pi_arg_ty_not_sort(ty, &tyty, e)
                })?;
                self.0.push(ty.as_ref().clone());
                let e_sort = self.infer_ty(e)?.normalize().into_sort().map_err(|ety| {
                    self.pi_e_ty_not_sort(ty, &ty_sort, e, &ety)
                })?;
                self.0.pop();
                Ok(Term::Sort(Univ::Var(None, {
                    let mut checker = CONSTRAINT_CHECKER.lock();
                    let v = checker.fresh_var();
                    checker.insert_constraint(Constraint {
                        left: Univ::Max(vec![ty_sort, e_sort]),
                        c: ConstraintType::Lt,
                        right: v.into(),
                    })?;
                    v
                })))
            },
            Term::IRCode(t) => match self.infer_ty(t)?.normalize() {
                Term::Sort(t) => {
                    let mut checker = CONSTRAINT_CHECKER.lock();
                    let v = checker.fresh_var();
                    checker.insert_constraint(Constraint {
                        left: t,
                        c: ConstraintType::Lt,
                        right: v.into(),
                    })?;
                    Ok(v.into())
                },
                ty => Err(self.ir_code_not_sort(t, &ty)),
            },
            Term::IRElement(d) => Ok(Term::IRCode(Box::new(self.infer_ty(d)?))),
            Term::IRChoose(a, f) => {
                let a_sort = self.infer_ty(a)?.normalize().into_sort().map_err(|aty| {
                    self.ir_choose_a_not_sort(a, &aty, f)
                })?;
                self.0.push(a_sort.clone().into());
                let (pty, out) = self.infer_ty(f)?.normalize().into_pi().map_err(|fty| {
                    self.ir_choose_fty_not_pi(a, &a_sort, f, &fty)
                })?;
                ensure!(pty == **a, self.ir_choose_pty_not_a(
                    a,
                    &a_sort,
                    f,
                    &pty,
                    &out,
                ));
                let out = match out {
                    Term::IRCode(mut out) => {
                        out.shift(-2, 0);
                        let out_sort = self.infer_ty(&out)?.into_sort().map_err(|outty| {
                            self.ir_choose_outty_not_sort(a, &a_sort, f, &pty, &out, &outty)
                        })?;
                        CONSTRAINT_CHECKER.lock().insert_constraint(Constraint {
                            left: a_sort,
                            c: ConstraintType::Le,
                            right: out_sort,
                        })?;
                        Term::IRCode(out)
                    },
                    out => bail!(self.ir_choose_f_out_not_ir_code(a, &a_sort, f, &pty, &out)),
                };
                self.0.pop();
                Ok(out)
            },
            Term::IRRecurse(i, r) => {
                let i_sort = self.infer_ty(i)?.normalize().into_sort().map_err(|ity| {
                    self.ir_rec_i_not_sort(i, &ity, r)
                })?;
                self.0.push(Term::Sort(i_sort.clone()));
                let (pty, mut out) = self.infer_ty(r)?.normalize().into_pi().map_err(|rty| {
                    self.ir_rec_rty_not_pi(i, &i_sort, r, &rty)
                })?;
                ensure!(matches!(out, Term::IRCode(_)), self.ir_rec_out_not_code(t, &out));
                let (ppty, pout) = pty.into_pi().map_err(|pty| {
                    self.ir_rec_pty_not_pi(i, &i_sort, r, &pty, &out)
                })?;
                ensure!(ppty >= **i, self.ir_rec_ppty_not_i(t, i, &ppty));
                if let Term::IRCode(out) = &mut out {
                    ensure!(out.as_ref() == &pout, self.ir_rec_pout_not_out(t, out, &pout));
                    out.shift(-2, 0);
                    let out_sort = self.infer_ty(out)?.normalize().into_sort().map_err(|outty| {
                        self.ir_rec_out_ty_not_sort(t, out, &outty)
                    })?;
                    CONSTRAINT_CHECKER.lock().insert_constraint(Constraint {
                        left: i_sort,
                        c: ConstraintType::Le,
                        right: out_sort,
                    })?;
                }
                self.0.pop();
                Ok(out)
            },
            Term::Constr(d, code) => {
                let rc = &mut *d.borrow_mut();
                let d = if let Some(d) = rc.as_ref() {
                    d.clone()
                } else {
                    let codety = match self.infer_ty(code)?.normalize() {
                        Term::IRCode(codety) => codety,
                        codety => bail!(self.ir_constr_codety_not_code(t, code, &codety)),
                    };
                    *rc = Some(codety.clone());
                    codety
                };
                let mut d2 = d.clone();
                d2.shift(1, 0);
                let (v1, v2) = {
                    let mut checker = CONSTRAINT_CHECKER.lock();
                    (checker.fresh_var(), checker.fresh_var())
                };
                Ok(d2.pi(Term::Sort(Univ::Var(None, v1))).pi(
                    Term::Sort(Univ::Var(None, v2))
                ))
            },
            Term::Bool => Ok((*BOOL_TYPE).into()),
            Term::Tt | Term::Ff => Ok(Term::Bool),
            Term::Ite(ty) => {
                self.infer_ty(ty)?;
                Ok(Term::Bool.pi(
                    {
                        let mut ty = ty.clone();
                        ty.shift(1, 0);
                        ty
                    }.pi({
                        let mut ty = ty.clone();
                        ty.shift(2, 0);
                        ty
                    }.pi({
                        let mut ty = ty.clone();
                        ty.shift(3, 0);
                        *ty
                    }))
                ))
            },
            Term::Unit => Ok((*UNIT_TYPE).into()),
            Term::Star => Ok(Term::Unit),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::DerefMut;
    use super::*;

    fn fresh_checker() -> impl DerefMut<Target = UniChecker> {
        let mut checker = CONSTRAINT_CHECKER.lock();
        *checker = Default::default();
        checker
    }

    fn fresh_var() -> Var {
        CONSTRAINT_CHECKER.lock().fresh_var()
    }

    fn checker_consistency() -> MResult<()> {
        let checker = CONSTRAINT_CHECKER.lock();
        checker.is_consistent().map_err(|c| miette!("{}", checker.create_dot_report(&c)))
    }

    #[test]
    fn ite() -> MResult<()> {
        fresh_checker();
        let t1 = Term::Bool.ite().app(Term::Tt).app(Term::Ff).app(Term::Tt);
        let t2 = Term::Bool.ite().app(Term::Ff).app(Term::Ff).app(Term::Tt);
        let mut ctx = Context::default();
        assert_eq!(ctx.infer_ty(&t1)?.normalize(), ctx.infer_ty(&t2)?.normalize());
        assert_eq!(t1.normalize(), Term::Ff);
        assert_eq!(t2.normalize(), Term::Tt);
        checker_consistency()
    }

    #[test]
    fn nat_ir_code() -> MResult<()> {
        fresh_checker();
        let nat_code = Term::Bool.ir_choose(Term::Bool.lam(Term::Unit.ir_code().ite()
            .app(Term::Bound(0))
            .app(Term::Star.ir_elem())
            .app(Term::Unit.ir_recurse(Term::Unit.pi(Term::Unit).lam(Term::Star.ir_elem()))),
        ));
        let mut ctx = Context::default();
        assert_eq!(ctx.infer_ty(&nat_code)?.normalize(), Term::Unit.ir_code());
        let constr = nat_code.constr().app(Term::Unit.lam(Term::Sort(
            Univ::Var(None, fresh_var())
        )));
        assert!(matches!(ctx.infer_ty(&constr)?.normalize(), Term::Sort(_)));
        println!("{:#?}", constr.normalize());
        checker_consistency()
    }
}
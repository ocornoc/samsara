use std::cell::RefCell;
use miette::{miette, ensure, bail, Result as MResult, Error as Report};
use lazy_static::lazy_static;
use parking_lot::Mutex;
pub use univ::*;

lazy_static! {
    static ref CONSTRAINT_CHECKER: Mutex<UniChecker> = Default::default();
}

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
    Constr(RefCell<Option<Box<Term>>>, Box<Term>),
}

impl Term {
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
            Term::IRCode(e) | Term::IRElement(e) => {
                e.shift(by, cutoff);
            },
            Term::Constr(ty, e) => {
                e.shift(by, cutoff);
                if let Some(ty) = ty.borrow_mut().as_mut() {
                    ty.shift(by, cutoff);
                }
            }
        }
    }

    pub fn subst(&mut self, db: DeBruijn, t: &Term) {
        match self {
            &mut Term::Bound(b) if b == db => {
                self.clone_from(t);
            },
            Term::Bound(_) | Term::Level => (),
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
            Term::IRCode(e) | Term::IRElement(e) => {
                e.subst(db, t);
            },
            Term::Constr(ty, e) => {
                e.subst(db, t);
                if let Some(ty) = ty.borrow_mut().as_mut() {
                    ty.subst(db, t);
                }
            }
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
                if let Term::Lam(ty, e) = l.as_mut() {
                    if matches!(**ty, Term::Level) {
                        r.normalize_mut();
                    }
                    e.subst(0, r);
                    e.shift(-1, 1);
                    e.normalize_mut();
                    *self = e.as_ref().clone();
                } else if let Term::Constr(ty, code) = l.as_mut() {
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
                            left = Term::Constr(ty.clone(), left.into());
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
                            let mut term = Term::Constr(
                                ty.clone(),
                                Term::App(v, Term::Bound(1).into()).into(),
                            );
                            term = Term::App(term.into(), r.clone()).normalize();
                            term = Term::Pi(
                                Term::Pi(i1, Term::App(r, Term::App(
                                    Term::Bound(1).into(),
                                    Term::Bound(0).into(),
                                ).into()).normalize().into()).into(),
                                term.into(),
                            );
                            let ty = ty.get_mut().as_mut().unwrap().clone();
                            *self = Term::Pi(
                                Term::Pi(i.clone(), ty).into(),
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
            }
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
        ppty: &Term,
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
                    right: Univ::Var(None, v),
                })?;
                Ok(Term::Sort(Univ::Var(None, v)))
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
                    right: Univ::Var(None, v),
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
                Ok(Term::Pi(ty.clone(), Box::new(e)))
            },
            Term::App(l, r) => match self.infer_ty(l)?.normalize() {
                Term::Pi(ll, lr) => {
                    let rty = self.infer_ty(r)?.normalize();
                    if *ll != rty {
                        Err(self.app_arg_ty_not_ll(l, r, &ll, &lr, &rty))
                    } else {
                        Ok(*lr)
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
                        right: Univ::Var(None, v),
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
                        right: Univ::Var(None, v),
                    })?;
                    Ok(Term::Sort(Univ::Var(None, v)))
                },
                ty => Err(self.ir_code_not_sort(t, &ty)),
            },
            Term::IRElement(d) => Ok(Term::IRCode(Box::new(self.infer_ty(d)?))),
            Term::IRChoose(a, f) => {
                let a_sort = self.infer_ty(a)?.normalize().into_sort().map_err(|aty| {
                    self.ir_choose_a_not_sort(a, &aty, f)
                })?;
                self.0.push(Term::Sort(a_sort.clone()));
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
                let (ppty, pout) = self.infer_ty(&pty)?.into_pi().map_err(|ppty| {
                    self.ir_rec_pty_not_pi(i, &i_sort, r, &pty, &out, &ppty)
                })?;
                ensure!(ppty == **i, self.ir_rec_ppty_not_i(t, i, &ppty));
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
                let mut d = if let Some(d) = d.borrow().as_ref() {
                    d.clone()
                } else {
                    let codety = match self.infer_ty(code)?.normalize() {
                        Term::IRCode(codety) => codety,
                        codety => bail!(self.ir_constr_codety_not_code(t, code, &codety)),
                    };
                    *d.borrow_mut() = Some(codety.clone());
                    codety
                };
                d.shift(1, 0);
                let (v1, v2) = {
                    let mut checker = CONSTRAINT_CHECKER.lock();
                    (checker.fresh_var(), checker.fresh_var())
                };
                Ok(Term::Pi(code.clone(), Term::Pi(
                    Term::Pi(d, Term::Sort(Univ::Var(None, v1)).into()).into(),
                    Term::Sort(Univ::Var(None, v2)).into(),
                ).into()))
            },
        }
    }
}
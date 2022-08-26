#![allow(dead_code)]
#![allow(unused_variables)]
//! Utility traits, functions used in the crate.
//!

use halo2_proofs::{ arithmetic::{Field as Halo2Field, FieldExt}, plonk::Expression};
use halo2_proofs::circuit::AssignedCell;
use pairing::{
    bn256::{Fq, Fr},
    group::ff::PrimeField,
};


/// Returns the sum of the passed in cells
pub mod sum {
    use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};
    use crate::util::Expr;

    /// Returns an expression for the sum of the list of expressions.
    pub fn expr<F: FieldExt, E: Expr<F>, I: IntoIterator<Item = E>>(inputs: I) -> Expression<F> {
        inputs
            .into_iter()
            .fold(0.expr(), |acc, input| acc + input.expr())
    }

    /// Returns the sum of the given list of values within the field.
    pub fn value<F: FieldExt>(values: &[u8]) -> F {
        values
            .iter()
            .fold(F::zero(), |acc, value| acc + F::from(*value as u64))
    }
}

/// Returns `1` when `expr[0] && expr[1] && ... == 1`, and returns `0`
/// otherwise. Inputs need to be boolean
pub mod and {
    use crate::util::Expr;
    use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};

    /// Returns an expression that evaluates to 1 only if all the expressions in
    /// the given list are 1, else returns 0.
    pub fn expr<F: FieldExt, E: Expr<F>, I: IntoIterator<Item = E>>(inputs: I) -> Expression<F> {
        inputs
            .into_iter()
            .fold(1.expr(), |acc, input| acc * input.expr())
    }

    /// Returns the product of all given values.
    pub fn value<F: FieldExt>(inputs: Vec<F>) -> F {
        inputs.iter().fold(F::one(), |acc, input| acc * input)
    }
}

/// Returns `1` when `expr[0] || expr[1] || ... == 1`, and returns `0`
/// otherwise. Inputs need to be boolean
pub mod or {
    use super::{and, not};
    use crate::util::Expr;
    use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};

    /// Returns an expression that evaluates to 1 if any expression in the given
    /// list is 1. Returns 0 if all the expressions were 0.
    pub fn expr<F: FieldExt, E: Expr<F>, I: IntoIterator<Item = E>>(inputs: I) -> Expression<F> {
        not::expr(and::expr(inputs.into_iter().map(not::expr)))
    }

    /// Returns the value after passing all given values through the OR gate.
    pub fn value<F: FieldExt>(inputs: Vec<F>) -> F {
        not::value(and::value(inputs.into_iter().map(not::value).collect()))
    }
}

/// Returns `1` when `b == 0`, and returns `0` otherwise.
/// `b` needs to be boolean
pub mod not {
    use crate::util::Expr;
    use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};

    /// Returns an expression that represents the NOT of the given expression.
    pub fn expr<F: FieldExt, E: Expr<F>>(b: E) -> Expression<F> {
        1.expr() - b.expr()
    }

    /// Returns a value that represents the NOT of the given value.
    pub fn value<F: FieldExt>(b: F) -> F {
        F::one() - b
    }
}

/// Returns `when_true` when `selector == 1`, and returns `when_false` when
/// `selector == 0`. `selector` needs to be boolean.
pub mod select {
    use crate::util::Expr;
    use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};

    /// Returns the `when_true` expression when the selector is true, else
    /// returns the `when_false` expression.
    pub fn expr<F: FieldExt>(
        selector: Expression<F>,
        when_true: Expression<F>,
        when_false: Expression<F>,
    ) -> Expression<F> {
        selector.clone() * when_true + (1.expr() - selector) * when_false
    }

    /// Returns the `when_true` value when the selector is true, else returns
    /// the `when_false` value.
    pub fn value<F: FieldExt>(selector: F, when_true: F, when_false: F) -> F {
        selector * when_true + (F::one() - selector) * when_false
    }

    /// Returns the `when_true` word when selector is true, else returns the
    /// `when_false` word.
    pub fn value_word<F: FieldExt>(
        selector: F,
        when_true: [u8; 32],
        when_false: [u8; 32],
    ) -> [u8; 32] {
        if selector == F::one() {
            when_true
        } else {
            when_false
        }
    }
}

/// Trait that implements functionality to get a constant expression from
/// commonly used types.
pub trait Expr<F: FieldExt> {
    /// Returns an expression for the type.
    fn expr(&self) -> Expression<F>;
}

/// Implementation trait `Expr` for type able to be casted to u64
#[macro_export]
macro_rules! impl_expr {
    ($type:ty) => {
        impl<F: halo2_proofs::arithmetic::FieldExt> $crate::util::Expr<F> for $type {
            #[inline]
            fn expr(&self) -> Expression<F> {
                Expression::Constant(F::from(*self as u64))
            }
        }
    };
    ($type:ty, $method:path) => {
        impl<F: halo2_proofs::arithmetic::FieldExt> $crate::util::Expr<F> for $type {
            #[inline]
            fn expr(&self) -> Expression<F> {
                Expression::Constant(F::from($method(self) as u64))
            }
        }
    };
}

impl_expr!(bool);
impl_expr!(u8);
impl_expr!(u64);
impl_expr!(usize);

pub trait Field: FieldExt + Halo2Field + PrimeField<Repr = [u8; 32]> {}

// Impl custom `Field` trait for BN256 Fr to be used and consistent with the
// rest of the workspace.
impl Field for Fr {}

// Impl custom `Field` trait for BN256 Frq to be used and consistent with the
// rest of the workspace.
impl Field for Fq {}


/// Restrict an expression to be a boolean.
pub fn bool_check<F: Field>(value: Expression<F>) -> Expression<F> {
    range_check(value, 2)
}

/// Restrict an expression such that 0 <= word < range.
pub fn range_check<F: Field>(word: Expression<F>, range: usize) -> Expression<F> {
    (1..range).fold(word.clone(), |acc, i| {
        acc * (Expression::Constant(F::from(i as u64)) - word.clone())
    })
}

impl<F: FieldExt> Expr<F> for Expression<F> {
    #[inline]
    fn expr(&self) -> Expression<F> {
        self.clone()
    }
}

impl<F: FieldExt> Expr<F> for &Expression<F> {
    #[inline]
    fn expr(&self) -> Expression<F> {
        (*self).clone()
    }
}

impl<F: FieldExt> Expr<F> for i32 {
    #[inline]
    fn expr(&self) -> Expression<F> {
        Expression::Constant(
            F::from(self.unsigned_abs() as u64)
                * if self.is_negative() {
                    -F::one()
                } else {
                    F::one()
                },
        )
    }
}

/// Given a bytes-representation of an expression, it computes and returns the
/// single expression.
pub fn expr_from_bytes<F: FieldExt, E: Expr<F>>(bytes: &[E]) -> Expression<F> {
    let mut value = 0.expr();
    let mut multiplier = F::one();
    for byte in bytes.iter() {
        value = value + byte.expr() * multiplier;
        multiplier *= F::from(256);
    }
    value
}

/// Returns 2**by as FieldExt
pub fn pow_of_two<F: FieldExt>(by: usize) -> F {
    F::from(2).pow(&[by as u64, 0, 0, 0])
}

#[allow(dead_code)]
/// An assigned cell in the circuit.
#[derive(Clone, Debug)]
pub struct Variable<T, F: Field> {
    assig_cell: AssignedCell<F, F>,
    value: Option<T>,
}

impl<T, F: Field> Variable<T, F> {
    pub(crate) fn new(assig_cell: AssignedCell<F, F>, value: Option<T>) -> Self {
        Self { assig_cell, value }
    }
}
fn main() {
    println!("hello world")
}
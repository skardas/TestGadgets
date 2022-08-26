//! IsZero gadget works as follows:
//!
//! Given a `value` to be checked if it is zero:
//!  - witnesses `inv0(value)`, where `inv0(x)` is 0 when `x` = 0, and
//!  `1/x` otherwise

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Region, Layouter, SimpleFloorPlanner},
    dev::MockProver,
    pairing::bn256::Fr as Fp,
    plonk::{Advice, Expression, VirtualCells, Circuit, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

pub mod util;

use util::Expr;

/// Trait that needs to be implemented for any gadget or circuit that wants to
/// implement `IsZero`.
pub trait IsZeroInstruction<F: FieldExt> {
    /// Given a `value` to be checked if it is zero:
    ///   - witnesses `inv0(value)`, where `inv0(x)` is 0 when `x` = 0, and
    ///     `1/x` otherwise
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Option<F>,
    ) -> Result<(), Error>;
}

/// Config struct representing the required fields for an `IsZero` config to
/// exist.
#[derive(Clone, Debug)]
pub struct IsZeroConfig<F> {
    /// Modular inverse of the value.
    pub value_inv: Column<Advice>,
    /// This can be used directly for custom gate at the offset if `is_zero` is
    /// called, it will be 1 if `value` is zero, and 0 otherwise.
    pub is_zero_expression: Expression<F>,
}

impl<F: FieldExt> IsZeroConfig<F> {
    /// Returns the is_zero expression
    pub fn expr(&self) -> Expression<F> {
        self.is_zero_expression.clone()
    }
}

/// Wrapper arround [`IsZeroConfig`] for which [`Chip`] is implemented.
pub struct IsZeroChip<F> {
    config: IsZeroConfig<F>,
}

#[rustfmt::skip]
impl<F: FieldExt> IsZeroChip<F> {
    /// Sets up the configuration of the chip by creating the required columns
    /// and defining the constraints that take part when using `is_zero` gate.
    ///
    /// Truth table of iz_zero gate:
    /// +----+-------+-----------+-----------------------+---------------------------------+-------------------------------------+
    /// | ok | value | value_inv | 1 - value ⋅ value_inv | value ⋅ (1 - value ⋅ value_inv) | value_inv ⋅ (1 - value ⋅ value_inv) |
    /// +----+-------+-----------+-----------------------+---------------------------------+-------------------------------------+
    /// | V  | 0     | 0         | 1                     | 0                               | 0                                   |
    /// |    | 0     | x         | 1                     | 0                               | x                                   |
    /// |    | x     | 0         | 1                     | x                               | 0                                   |
    /// | V  | x     | 1/x       | 0                     | 0                               | 0                                   |
    /// |    | x     | y         | 1 - xy                | x(1 - xy)                       | y(1 - xy)                           |
    /// +----+-------+-----------+-----------------------+---------------------------------+-------------------------------------+
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value_inv: Column<Advice>,
    ) -> IsZeroConfig<F> {
        // dummy initialization
        let mut is_zero_expression = 0.expr();

        meta.create_gate("is_zero gate", |meta| {
            let q_enable = q_enable(meta);

            let value_inv = meta.query_advice(value_inv, Rotation::cur());
            let value = value(meta);

            is_zero_expression = 1.expr() - value.clone() * value_inv;

            // We wish to satisfy the below constrain for the following cases:
            //
            // 1. value == 0
            // 2. if value != 0, require is_zero_expression == 0 => value_inv == value.invert()
            [q_enable * value * is_zero_expression.clone()]
        });

        IsZeroConfig::<F> {
            value_inv,
            is_zero_expression,
        }
    }

    /// Given an `IsZeroConfig`, construct the chip.
    pub fn construct(config: IsZeroConfig<F>) -> Self {
        IsZeroChip { config }
    }
}

impl<F: FieldExt> IsZeroInstruction<F> for IsZeroChip<F> {
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Option<F>,
    ) -> Result<(), Error> {
        let config = self.config();

        let value_invert = value.map(|value| value.invert().unwrap_or(F::zero()));
        region.assign_advice(
            || "witness inverse of value",
            config.value_inv,
            offset,
            || value_invert.ok_or(Error::Synthesis),
        )?;

        Ok(())
    }
}

impl<F: FieldExt> Chip<F> for IsZeroChip<F> {
    type Config = IsZeroConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[derive(Clone, Debug)]
struct TestCircuitConfig<F> {
    q_enable: Selector,
    value: Column<Advice>,
    check: Column<Advice>,
    is_zero: IsZeroConfig<F>,
}

#[derive(Default)]
struct TestCircuit<F: FieldExt> {
    values: Option<Vec<u64>>,
    // checks[i] = is_zero(values[i + 1] - values[i])
    checks: Option<Vec<bool>>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
    type Config = TestCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_enable = meta.complex_selector();
        let value = meta.advice_column();
        let value_diff_inv = meta.advice_column();
        let check = meta.advice_column();

        let is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                let value_prev = meta.query_advice(value, Rotation::prev());
                let value_cur = meta.query_advice(value, Rotation::cur());
                value_cur - value_prev
            },
            value_diff_inv,
        );

        let config = Self::Config {
            q_enable,
            value,
            check,
            is_zero,
        };

        meta.create_gate("check is_zero", |meta| {
            let q_enable = meta.query_selector(q_enable);

            // This verifies is_zero is calculated correctly
            let check = meta.query_advice(config.check, Rotation::cur());

            vec![q_enable * (config.is_zero.is_zero_expression.clone() - check)]
        });

        config
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = IsZeroChip::construct(config.is_zero.clone());

        let values: Vec<_> = self
            .values
            .as_ref()
            .map(|values| values.iter().map(|value| F::from(*value)).collect())
            .ok_or(Error::Synthesis)?;
        let checks = self.checks.as_ref().ok_or(Error::Synthesis)?;
        let (first_value, values) = values.split_at(1);
        let first_value = first_value[0];

        layouter.assign_region(
            || "witness",
            |mut region| {
                region.assign_advice(
                    || "first row value",
                    config.value,
                    0,
                    || Ok(first_value),
                )?;

                let mut value_prev = first_value;
                for (idx, (value, check)) in values.iter().zip(checks).enumerate() {
                    region.assign_advice(
                        || "check",
                        config.check,
                        idx + 1,
                        || Ok(F::from(*check as u64)),
                    )?;
                    region.assign_advice(
                        || "value",
                        config.value,
                        idx + 1,
                        || Ok(*value),
                    )?;

                    config.q_enable.enable(&mut region, idx + 1)?;
                    chip.assign(&mut region, idx + 1, Some(*value - value_prev))?;

                    value_prev = *value;
                }

                Ok(())
            },
        )
    }
}

macro_rules! try_test_circuit {
        ($values:expr, $checks:expr, $result:expr) => {{
            // let k = usize::BITS - $values.len().leading_zeros();

            // TODO: remove zk blinding factors in halo2 to restore the
            // correct k (without the extra + 2).
            let k = usize::BITS - $values.len().leading_zeros() + 2;
            let circuit = TestCircuit::<Fp> {
                values: Some($values),
                checks: Some($checks),
                _marker: PhantomData,
            };
            let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }
fn main() {
    try_test_circuit!(
            vec![1, 2, 3, 4, 5],
            vec![false, false, false, false],
            Ok(())
        );
    try_test_circuit!(
            vec![1, 2, 2, 3, 3], //
            vec![false, true, false, true],
            Ok(())
        );
}
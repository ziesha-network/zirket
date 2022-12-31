NUMBER_RS = """
use bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::PrimeField;
use std::ops::*;

#[derive(Clone)]
pub struct Number<S: PrimeField> {
    pub lc: LinearCombination<S>,
    pub val: Option<S>,
}

impl<S: PrimeField> Number<S> {
    pub fn zero() -> Self {
        Self {
            lc: LinearCombination::zero(),
            val: Some(S::zero()),
        }
    }
    pub fn get_lc(&self) -> &LinearCombination<S> {
        &self.lc
    }
    pub fn get_value(&self) -> Option<S> {
        self.val.clone()
    }
    pub fn alloc<CS: ConstraintSystem<S>>(
        cs: &mut CS,
        val: Option<S>,
    ) -> Result<Number<S>, SynthesisError> {
        let v = cs.alloc(|| "", || val.ok_or(SynthesisError::AssignmentMissing))?;
        Ok(Self {
            lc: LinearCombination::<S>::zero() + v,
            val,
        })
    }
}

impl<S: PrimeField> Add<&Number<S>> for &Number<S> {
    type Output = Number<S>;

    fn add(self, other: &Number<S>) -> Self::Output {
        Self::Output {
            lc: self.lc.clone() + &other.lc,
            val: self.val.zip(other.val).map(|(slf, othr)| slf + othr),
        }
    }
}

impl<S: PrimeField> Add<(S, &Number<S>)> for &Number<S> {
    type Output = Number<S>;

    fn add(self, other: (S, &Number<S>)) -> Self::Output {
        Self::Output {
            lc: self.lc.clone() + (other.0, &other.1.lc),
            val: self
                .val
                .zip(other.1.val)
                .map(|(slf, othr)| slf + other.0 * othr),
        }
    }
}
"""

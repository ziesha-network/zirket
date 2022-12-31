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
    pub fn add_constant<CS: ConstraintSystem<S>>(&mut self, num: S) {
        self.lc = self.lc.clone() + (num, CS::one());
        self.val = self.val.map(|v| v + num);
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

impl<S: PrimeField> Sub<&Number<S>> for &Number<S> {
    type Output = Number<S>;

    fn sub(self, other: &Number<S>) -> Self::Output {
        Self::Output {
            lc: self.lc.clone() - &other.lc,
            val: self.val.zip(other.val).map(|(slf, othr)| slf - othr),
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

UINT_RS = """
use super::Number;
use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::{PrimeField, PrimeFieldBits};

#[derive(Clone)]
pub struct UnsignedInteger<S: PrimeField + PrimeFieldBits> {
    bits: Vec<AllocatedBit>,
    num: Number<S>,
}

impl<S: PrimeField + PrimeFieldBits> UnsignedInteger<S> {
    pub fn get_lc(&self) -> &LinearCombination<S> {
        self.num.get_lc()
    }
    pub fn get_number(&self) -> &Number<S> {
        &self.num
    }
    pub fn get_value(&self) -> Option<S> {
        self.num.get_value()
    }
    pub fn bits(&self) -> &Vec<AllocatedBit> {
        &self.bits
    }
    pub fn num_bits(&self) -> usize {
        self.bits.len()
    }
    pub fn alloc<CS: ConstraintSystem<S>>(
        cs: &mut CS,
        val: S,
        bits: usize,
    ) -> Result<Self, SynthesisError> {
        let alloc = Number::<S>::alloc(&mut *cs, Some(val))?;
        Self::constrain(cs, alloc.into(), bits)
    }
    pub fn alloc_32<CS: ConstraintSystem<S>>(
        cs: &mut CS,
        val: u32,
    ) -> Result<Self, SynthesisError> {
        Self::alloc(cs, S::from(val as u64), 32)
    }
    pub fn alloc_64<CS: ConstraintSystem<S>>(
        cs: &mut CS,
        val: u64,
    ) -> Result<Self, SynthesisError> {
        Self::alloc(cs, S::from(val), 64)
    }
    pub fn constrain<CS: ConstraintSystem<S>>(
        cs: &mut CS,
        num: Number<S>,
        num_bits: usize,
    ) -> Result<Self, SynthesisError> {
        let mut bits = Vec::new();
        let mut coeff = S::one();
        let mut all = LinearCombination::<S>::zero();
        let bit_vals: Option<Vec<bool>> = num
            .get_value()
            .map(|v| v.to_le_bits().iter().map(|b| *b).collect());
        for i in 0..num_bits {
            let bit = AllocatedBit::alloc(&mut *cs, bit_vals.as_ref().map(|b| b[i]))?;
            all = all + (coeff, bit.get_variable());
            bits.push(bit);
            coeff = coeff.double();
        }
        cs.enforce(
            || "check",
            |lc| lc + &all,
            |lc| lc + CS::one(),
            |lc| lc + num.get_lc(),
        );

        Ok(Self { num, bits })
    }

    // ~198 constraints
    pub fn lt<CS: ConstraintSystem<S>>(
        &self,
        cs: &mut CS,
        other: &UnsignedInteger<S>,
    ) -> Result<Boolean, SynthesisError> {
        assert_eq!(self.num_bits(), other.num_bits());
        let num_bits = self.num_bits();

        // Imagine a and b are two sigend (num_bits + 1) bits numbers
        let two_bits = S::from(2).pow_vartime(&[num_bits as u64 + 1, 0, 0, 0]);
        let mut sub = &self.num - &other.num;
        sub.add_constant::<CS>(two_bits);

        let sub_bits = UnsignedInteger::<S>::constrain(&mut *cs, sub, num_bits + 2)?;
        Ok(Boolean::Is(sub_bits.bits()[num_bits].clone()))
    }

    pub fn gt<CS: ConstraintSystem<S>>(
        &self,
        cs: &mut CS,
        other: &UnsignedInteger<S>,
    ) -> Result<Boolean, SynthesisError> {
        other.lt(cs, self)
    }

    pub fn lte<CS: ConstraintSystem<S>>(
        &self,
        cs: &mut CS,
        other: &UnsignedInteger<S>,
    ) -> Result<Boolean, SynthesisError> {
        Ok(self.gt(cs, other)?.not())
    }

    pub fn gte<CS: ConstraintSystem<S>>(
        &self,
        cs: &mut CS,
        other: &UnsignedInteger<S>,
    ) -> Result<Boolean, SynthesisError> {
        Ok(self.lt(cs, other)?.not())
    }
}
"""

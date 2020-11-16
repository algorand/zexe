use algebra_core::Field;
use r1cs_core::{Namespace, SynthesisError};
use r1cs_std::prelude::*;

use crate::{
    crh::{FixedLengthCRH, FixedLengthCRHGadget},
    merkle_tree::*,
};

use core::borrow::Borrow;

pub struct PathVar<P, HGadget, ConstraintF>
where
    P: Config,
    HGadget: FixedLengthCRHGadget<P::H, ConstraintF>,
    ConstraintF: Field,
{
    path: Vec<(HGadget::OutputVar, HGadget::OutputVar)>,
}

impl<P, CRHGadget, ConstraintF> PathVar<P, CRHGadget, ConstraintF>
where
    P: Config,
    ConstraintF: Field,
    CRHGadget: FixedLengthCRHGadget<P::H, ConstraintF>,
    <CRHGadget::OutputVar as R1CSVar<ConstraintF>>::Value: PartialEq,
{
    #[tracing::instrument(target = "r1cs", skip(self, parameters, root, leaf))]
    pub fn check_membership(
        &self,
        parameters: &CRHGadget::ParametersVar,
        root: &CRHGadget::OutputVar,
        leaf: impl ToBytesGadget<ConstraintF>,
    ) -> Result<Boolean<ConstraintF>, SynthesisError> {
        assert_eq!(self.path.len(), P::HEIGHT - 1);
        // Check that the hash of the given leaf matches the leaf hash in the membership
        // proof.
        let leaf_bits = leaf.to_bytes()?;
        let leaf_hash = CRHGadget::evaluate(parameters, &leaf_bits)?;
        let cs = leaf_hash.cs().or(root.cs());

        // Check if leaf is one of the bottom-most siblings.
        let leaf_is_left = Boolean::new_witness(r1cs_core::ns!(cs, "leaf_is_left"), || {
            Ok(leaf_hash.value()?.eq(&self.path[0].0.value()?))
        })?;

        let mut result =
            leaf_hash.is_eq(&leaf_is_left.select(&self.path[0].0, &self.path[0].1)?)?;

        // Check levels between leaf level and root.
        let mut previous_hash = leaf_hash;
        for &(ref left_hash, ref right_hash) in &self.path {
            // Check if the previous_hash matches the correct current hash.
            let previous_is_left =
                Boolean::new_witness(r1cs_core::ns!(cs, "previous_is_left"), || {
                    Ok(previous_hash.value()?.eq(&left_hash.value()?))
                })?;

            let ns = r1cs_core::ns!(cs, "enforcing that inner hash is correct");
            let equality_cmp = previous_is_left.select(left_hash, right_hash)?;
            result = result.and(&previous_hash.is_eq(&equality_cmp)?)?;
            drop(ns);

            previous_hash =
                hash_inner_node::<P::H, CRHGadget, ConstraintF>(parameters, left_hash, right_hash)?;
        }

        result.and(&root.is_eq(&previous_hash)?)
    }

    #[tracing::instrument(
        target = "r1cs",
        skip(self, parameters, old_root, new_root, old_leaf, new_leaf)
    )]
    pub fn check_membership_and_update(
        &self,
        parameters: &CRHGadget::ParametersVar,
        old_root: &CRHGadget::OutputVar,
        new_root: &CRHGadget::OutputVar,
        old_leaf: impl ToBytesGadget<ConstraintF>,
        new_leaf: impl ToBytesGadget<ConstraintF>,
    ) -> Result<Boolean<ConstraintF>, SynthesisError> {
        assert_eq!(self.path.len(), P::HEIGHT - 1);
        // Hash the leaf.
        let old_leaf_bits = old_leaf.to_bytes()?;
        let old_leaf_hash = CRHGadget::evaluate(parameters, &old_leaf_bits)?;
        let cs = old_leaf_hash.cs().or(old_root.cs());
        let new_leaf_bits = new_leaf.to_bytes()?;
        let new_leaf_hash = CRHGadget::evaluate(parameters, &new_leaf_bits)?;

        // Check levels between leaf level and root.
        let mut result = Boolean::<ConstraintF>::TRUE;
        let mut previous_old_hash = old_leaf_hash;
        let mut previous_new_hash = new_leaf_hash;
        for &(ref old_left_hash, ref old_right_hash) in &self.path {
            // Check if the previous_old_hash matches the correct current hash.
            let previous_is_left =
                Boolean::new_witness(r1cs_core::ns!(cs, "previous_is_left"), || {
                    Ok(previous_old_hash.value()?.eq(&old_left_hash.value()?))
                })?;

            let ns = r1cs_core::ns!(cs, "enforcing that inner hash is correct");
            let equality_cmp = previous_is_left.select(old_left_hash, old_right_hash)?;
            result = result.and(&previous_old_hash.is_eq(&equality_cmp)?)?;

            // Compute the old hash for the next level
            previous_old_hash = hash_inner_node::<P::H, CRHGadget, ConstraintF>(
                parameters,
                &old_left_hash,
                &old_right_hash,
            )?;

            // Compute the new hash for the next level
            let new_left_hash = previous_is_left.select(&previous_new_hash, old_left_hash)?;
            let new_right_hash = previous_is_left.select(old_right_hash, &previous_new_hash)?;
            previous_new_hash = hash_inner_node::<P::H, CRHGadget, ConstraintF>(
                parameters,
                &new_left_hash,
                &new_right_hash,
            )?;
            drop(ns); // TODO: where should this go?
        }

        // check both roots
        result
            .and(&old_root.is_eq(&previous_old_hash)?)?
            .and(&new_root.is_eq(&previous_new_hash)?)
    }
}

pub(crate) fn hash_inner_node<H, HG, ConstraintF>(
    parameters: &HG::ParametersVar,
    left_child: &HG::OutputVar,
    right_child: &HG::OutputVar,
) -> Result<HG::OutputVar, SynthesisError>
where
    ConstraintF: Field,
    H: FixedLengthCRH,
    HG: FixedLengthCRHGadget<H, ConstraintF>,
{
    let left_bytes = left_child.to_bytes()?;
    let right_bytes = right_child.to_bytes()?;
    let mut bytes = left_bytes;
    bytes.extend_from_slice(&right_bytes);

    HG::evaluate(parameters, &bytes)
}

impl<P, HGadget, ConstraintF> AllocVar<Path<P>, ConstraintF> for PathVar<P, HGadget, ConstraintF>
where
    P: Config,
    HGadget: FixedLengthCRHGadget<P::H, ConstraintF>,
    ConstraintF: Field,
{
    fn new_variable<T: Borrow<Path<P>>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        f().and_then(|val| {
            let mut path = Vec::new();
            for &(ref l, ref r) in val.borrow().path.iter() {
                let l_hash = HGadget::OutputVar::new_variable(
                    r1cs_core::ns!(cs, "l_child"),
                    || Ok(l),
                    mode,
                )?;
                let r_hash = HGadget::OutputVar::new_variable(
                    r1cs_core::ns!(cs, "r_child"),
                    || Ok(r),
                    mode,
                )?;
                path.push((l_hash, r_hash));
            }
            Ok(PathVar { path })
        })
    }
}

#[cfg(test)]
mod test {
    use crate::{
        crh::{
            pedersen::{self, constraints::CRHGadget},
            FixedLengthCRH, FixedLengthCRHGadget,
        },
        merkle_tree::*,
    };
    use algebra::ed_on_bls12_381::{EdwardsProjective as JubJub, Fq};
    use r1cs_core::ConstraintSystem;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;
    use r1cs_std::ed_on_bls12_381::EdwardsVar;

    #[derive(Clone)]
    pub(super) struct Window4x256;
    impl pedersen::Window for Window4x256 {
        const WINDOW_SIZE: usize = 4;
        const NUM_WINDOWS: usize = 256;
    }

    type H = pedersen::CRH<JubJub, Window4x256>;
    type HG = CRHGadget<JubJub, EdwardsVar, Window4x256>;

    struct JubJubMerkleTreeParams;

    impl Config for JubJubMerkleTreeParams {
        const HEIGHT: usize = 32;
        type H = H;
    }

    type JubJubMerkleTree = MerkleTree<JubJubMerkleTreeParams>;

    fn generate_merkle_tree(leaves: &[[u8; 30]], use_bad_root: bool) -> () {
        let mut rng = XorShiftRng::seed_from_u64(9174123u64);

        let crh_parameters = H::setup(&mut rng).unwrap();
        let tree = JubJubMerkleTree::new(crh_parameters.clone(), leaves).unwrap();
        let root = tree.root();
        let cs = ConstraintSystem::<Fq>::new_ref();
        for (i, leaf) in leaves.iter().enumerate() {
            let proof = tree.generate_proof(i, &leaf).unwrap();
            assert!(proof.verify(&crh_parameters, &root, &leaf).unwrap());

            // Allocate Merkle Tree Root
            let root = <HG as FixedLengthCRHGadget<H, _>>::OutputVar::new_witness(
                r1cs_core::ns!(cs, "new_digest"),
                || {
                    if use_bad_root {
                        Ok(<H as FixedLengthCRH>::Output::default())
                    } else {
                        Ok(root)
                    }
                },
            )
            .unwrap();

            let constraints_from_digest = cs.num_constraints();
            println!("constraints from digest: {}", constraints_from_digest);

            // Allocate Parameters for CRH
            let crh_parameters = <HG as FixedLengthCRHGadget<H, Fq>>::ParametersVar::new_constant(
                r1cs_core::ns!(cs, "new_parameter"),
                &crh_parameters,
            )
            .unwrap();

            let constraints_from_parameters = cs.num_constraints() - constraints_from_digest;
            println!(
                "constraints from parameters: {}",
                constraints_from_parameters
            );

            // Allocate Leaf
            let leaf_g = UInt8::constant_vec(leaf);

            let constraints_from_leaf =
                cs.num_constraints() - constraints_from_parameters - constraints_from_digest;
            println!("constraints from leaf: {}", constraints_from_leaf);

            // Allocate Merkle Tree Path
            let cw =
                PathVar::<_, HG, _>::new_witness(r1cs_core::ns!(cs, "new_witness"), || Ok(&proof))
                    .unwrap();
            for (i, (l, r)) in cw.path.iter().enumerate() {
                assert_eq!(l.value().unwrap(), proof.path[i].0);
                assert_eq!(r.value().unwrap(), proof.path[i].1);
            }

            let constraints_from_path = cs.num_constraints()
                - constraints_from_parameters
                - constraints_from_digest
                - constraints_from_leaf;
            println!("constraints from path: {}", constraints_from_path);
            let leaf_g: &[_] = leaf_g.as_slice();
            cw.check_membership(&crh_parameters, &root, &leaf_g)
                .unwrap()
                .enforce_equal(&Boolean::TRUE)
                .unwrap();
            let setup_constraints = constraints_from_leaf
                + constraints_from_digest
                + constraints_from_parameters
                + constraints_from_path;
            println!(
                "number of constraints: {}",
                cs.num_constraints() - setup_constraints
            );
        }

        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn good_root_test() {
        let mut leaves = Vec::new();
        for i in 0..4u8 {
            let input = [i; 30];
            leaves.push(input);
        }
        generate_merkle_tree(&leaves, false);
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        let mut leaves = Vec::new();
        for i in 0..4u8 {
            let input = [i; 30];
            leaves.push(input);
        }
        generate_merkle_tree(&leaves, true);
    }
}

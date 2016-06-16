## Coq Proofs for STLC 1/2 ##


This directory contains mechanized proofs of safety properties in STLC 1/2. 

Use `make` to compile and verify all proof scripts. 


### File [stlc1.v](stlc1.v) ###

Language definition, type system, and operational semantics for STLC 1/2 (Sections 3.1, 3.2 in the paper).

- Language syntax (types `ty`, terms `tm`, values `vl`)
- Environments (`tenv`, `venv`), split according to 1st/2nd class entries, and with the possibility to restrict the visibility of entries (`sanitize_env`)
- Type Assignment (`has_type`)
- Operational semantics (`teval`)


### File [stlc2.v](stlc2.v) ###

Low-level semantics STLCs 1/2 (Section 3.3 in the paper), and its lifetime properties (Section 3.3 in the paper).

- Low-level language semantics (`teval_stack`)
- Values (`vl_stack`): closures contain a heap record (holding first-class values) 
						and a stack pointer (to resolve second class values)
- A `stack` consists of `stack_frame`s
- Well-formedness judgement for 1st/2nd class values and environments (`wf_val c`, `fc_env`, `sc_env`, here, `wf_val First c` corresponds to `fc` predicate in the paper)
- **Theorem**: (fc_eval): in first-class environments, 1/2 evaluation 
	produces 1/2-well-formed results (corresponds to Lemma 3.1 and Theorem 3.2 in the paper).
	
Note: We plan to update the statement of Lemma 3.1 and Theorem 3.2 in the paper to correspond more clearly to `fc_eval` in this file.

It follows that evaluation in STLCs 1/2 never leaks stack references (Theorem 3.2 in the paper).

### File [stlc3.v](stlc3.v) ###

Semantic equivalence between STLC 1/2 and STLCs 1/2 (Section 3.3 in the paper).

- Definition of correspondence relation(`equiv_val`,`equiv_env`, corresponds to `~` in the paper)
- **Theorem**: semantic equivalence (`teval_equiv`, corresponds to Theorem 3.3 in the paper)

It follows that lifetime properties proved in `stlc2.v` for STLCs 1/2 also hold for STLC 1/2. In particular, the lifetimes of second-class bindings in STLC 1/2 follow a stack discipline (Corollary 3.4 in the paper).

	
### File [stlc4.v](stlc4.v) ###

Type safety for STLC 1/2 (Section 3.4 in the paper).

- Value type assignment (`val_type`), 
- Well-typed runtime environments (`wf_env`)

- **Theorem**: type soundness (`full_safety`, corresponds to Theorem 3.5 in the paper)

It follows that all well-typed STLC 1/2 programs are guaranteed to respect stack-based lifetimes for second-class values (Corollary 3.6 in the paper). Via the semantic equivalence, the type soundness result for STLC 1/2 extends to STLCs 1/2.


## Coq Proofs for DSUB 1/2 ##

We extend our formal model with polymorphism and subtyping in System DSUB 1/2.

### File [dsub.v](dsub.v) ###

This file contains our Coq development for System DSUB 1/2 (Section 4.1 in the paper).

- Language syntax (types `ty`, terms `tm`, values `vl`)
- Type Assignment (`has_type`)
- Subtyping (static: `stp`, dynamic: `stp2`)
- Operational semantics (`teval`)
- **Theorem**: type soundness (`full_safety`, corresponds to Theorem 4.2 in the paper)

The type system and operational semantics are as described in the paper, and set up
like in the STLC 1/2 development.

One difference is in how we treat environments: in STLC 1/2 environments were split
into 1st and 2nd part, but here we use flat environments and add a 1st/2nd class tag
to each element, and also a boolean flag denoting whether the element is accessible.

Evaluation and type assignment remove 2nd-class items from the environment by
turning their access flags to false. Note however, that the dynamic subtyping
relation must ignore these flags in order to relate path-dependent types across
environments. Since this is only an invariant used in the soundness proof and
not part of the operational semantics, this is not a safety concern. 

The type soundness result shows that the type system correctly predicts the runtime
checks by the evaluator, which are the same as in STLC 1/2. It would be easy, 
but not very insightful, to redo the formal proof of semantic equivalence 
with a stack-based evaluator, as we have done for STLCs 1/2.







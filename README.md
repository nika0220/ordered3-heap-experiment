# Ordered3 Heap Experiment

This repository contains experimental code for a heap-like comparison sorting variant.

The maintained invariant is:

parent >= left child >= right child

The basic idea is to preserve sibling-order information physically in the heap layout.

In an ordinary binary heap, we usually keep only:

parent >= child

In this variant, each local triple is kept ordered:

parent >= left child >= right child

I currently call this structure an **ordered3 heap**.

## Current status

This is experimental code, not a production sorting library.

On random permutations of complete tree sizes:

n = 2^k - 1

the current version with spine-insertion build empirically shows roughly:

C(n) ≈ n log2(n) - 1.13n

comparisons.

This is an empirical observation, not a proved bound.

## High-level idea

The heap can be viewed as preserving sibling-order information.

There is also an asymmetric flow interpretation:

* During build, when a value is too small, it is pushed down along the left chain.
* During delete-max/pop, when a hole is created, the hole is pushed down using the right-side structure.

This separates the “value flow” used during build from the “hole flow” used during extraction.

## Files

* `ordered3_spine_insert_build_experiment.cpp`
  Complete-tree experiment with ordered3 heap and spine-insertion build.

* `ordered3_spine_insert_build_experiment_output.txt`
  Output log for the complete-tree experiment.

* `ordered3_padded_sentinel_experiment.cpp`
  General-n experiment using sentinel padding.

* `ordered3_padded_sentinel_experiment_output.txt`
  Output log for the sentinel-padding experiment.

* `ordered3_general_n_direct_rrepair.cpp`
  Direct general-n version for incomplete binary trees.

* `ordered3_general_n_direct_rrepair_output.txt`
  Output log for the direct general-n experiment.

## Related ideas

This appears related to:

* weak heaps
* fine heaps / heaps with bits
* bottom-up heapsort
* strong or strengthened heap variants

I am mainly looking for references, terminology, and corrections.

## Disclosure

This README and some explanatory text were drafted with help from ChatGPT based on my notes, code, and experimental results.

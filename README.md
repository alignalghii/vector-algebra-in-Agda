[(Back to central personal homepage)](https://alignalghii.github.io)

# Vector algebra in Agda

## Scope of the project: middle and long-term goals

The scope of this project is to be able to state and to prove theorems about vectors and matrices. Agda is used as a theorem prover.

### Matrix algebra on collision detection

The middle-term goal it to proceed to Fourier-Motzkin elimination, an algorithm known for solving a system of linear inequalities (i.e. solving several inequalities in several variables simultaneously).

As a linear equation determines a line, a linear inequality determines a half-plane, and a system of linear inequalities determines the intersection of several half-planes: a polygon! Thus such an inequality system can describe a convex polygon by “spanning” it with its holding half-planes. And a concave polygon can be represented as an union of appropriate constituent convex polygons.

In short: Fourier-Motzkin elimination is suitable for collision detection for arbitrary (polygonal) shapes, thus it can serve as a virtual physics engine for smaller simpler games and graphics editors.

### Complete formal specification and validation of a graphics editor with virtual physics

The ultimate long-goal of this project is to provide a formal and validity-proven specification of concrete collision detection based software: a floor-plan designer graphics editor for real estate agents: to ease the daily work of real estate employees by helping them to design the floor-plans of their flats on their own. A vector-graphics editor software tailored for the goal with specific features, most importantly collision detection, easy alignment of objects by sliding an colliding effects, handling wall openings (doors, windows, corridors), easy rearrangeability and modular build-up of a complete flat / house floorplan on all levels.

This project is only for the experimentation with the Agda formalization. The actual floor plan designer graphics editor software has [its own project](https://github.com/alignalghii/loosely-coupled-figure-editor), a practical development, without any formal validity proofs (a somewhat stuck “legacy” project currently waiting for some refactory).

## Current achievements: proving theorems on matrix transposition

Important links to project parts:

- Proving [equivalence of alternative definitions](https://github.com/alignalghii/vector-algebra-in-Agda/blob/main/Vec/Matrix/TranspositionAlternative.agda#L38) of matrix transposition
- Proving transposition [being self-inverse operation](https://github.com/alignalghii/vector-algebra-in-Agda/blob/main/Vec/Matrix/Transposition.agda#L50) (an *involution*)


In the first phase, a general versatility in treating vector and matrix algebra must be attained.

Said informally, maybe matrix transposition is one of the most prominent summarizing example to establish a milestone in versatility with general matrix algebra. Specifically, Fourier-Motzkin elimination will use it extensively, but independently of that aspect, this concept is a good test generalist subgoal as well. Thus, in the first phase the project tries to establish achievements in that.

### Equivalence of alternative definitions

There are two alternative definitions for matrix transposition. The first is the straightforward recursive definition (easy to handle computationally), the other is a less efficient, but (maybe) more spectacular and intuitive approach (easier for beginners to understand in a single step).

Both definitions are equivalent mathematically, although built up conceptually rather orthogonal.

The project makes both definitions, states their equivalence, and also **proves that the two approaches are equivalent**. The approaches present a kind of duality (probably not rigorously): they are rather orthogonal approaches, and that make the proof non-trivial. Their induction structure is entirely different (row- vs column-based), thus the proof is based on matrix extensionality.

### Algebraic property: involution — being self-inverse

Afterwards, the project begins to state and prove interesting properties of transposition itself as an algebraic operation. Till now, only a single such purely algebraic property is stated and proven: **transposition is an involution**: an *involutive* (= self-inverse) operation among matrices.

# Details of the proof

[Main argument](proof.md) · [Verify in Lean](lean/README.md)

These are the lattice-filling, counting, area and phase lemmas used in
[the proof](proof.md). The final calculation for 56 tiles and the
construction attaining 136 are given there.

<!-- Adapted from the authoritative technical-details.md, SHA-256 7651c98e502024fbaf118bd134424add7b9a11e4652d2fd5b34f80b26c085635. Exported 2026-10-09; publication edits only. -->

## 1. Model and lattice filling

### Lattice definitions and the no holes rule

A support is a finite nonempty set $\mathcal V\subset\mathbb Z^2$.
Its full contact graph $G$ includes every pair whose difference is one of
$(1,0),(0,1),(-1,1)$ or their negatives. These coordinates describe
hexagon centres. The initial counting formulas assume that $G$ is connected;
the separated-support reduction below removes this assumption.

The no-holes condition means that each unoccupied vertex can reach outside
every finite coordinate box by a finite path of unoccupied lattice
neighbours. This makes the empty-cell escape condition explicit; it is
not an assumed inequality about area or perimeter.

Define the elementary triangles

$$
 \Delta^+_{ij}=\{(i,j),(i+1,j),(i,j+1)\},\qquad
 \Delta^-_{ij}=\{(i+1,j),(i+1,j+1),(i,j+1)\}.
$$

Let $\mathcal T$ consist of those triangles whose three vertices are
occupied. Their edges all belong to $G$, by the full-contact assumption.
A triangle subset has boundary equal to the symmetric difference of its
three-edge boundaries. In particular, every such boundary has even degree.

We establish the required counting and colouring directly from finite
lattice data. No assertion about bounded plane faces is needed.

### Every finite even lattice edge set has a unique finite filling

In this paragraph addition is modulo two. Write $h_{ij},v_{ij},k_{ij}$
for the indicator bits of the horizontal, vertical and diagonal edges

$$
 \{(i,j),(i+1,j)\},\quad
 \{(i,j),(i,j+1)\},\quad
 \{(i+1,j),(i,j+1)\},
$$

respectively, in an arbitrary finite even edge set. Evenness at $(i,j)$
is precisely

$$
 h_{i-1,j}+h_{ij}+v_{i,j-1}+v_{ij}
       +k_{i-1,j}+k_{i,j-1}=0.
$$

Put $A_{ij}=h_{ij}+k_{ij}$, $B_{ij}=v_{ij}+k_{ij}$.
The preceding relation gives the local identity

$$
 A_{ij}+A_{i-1,j}=B_{ij}+B_{i,j-1}.
$$

Define the down-triangle and up-triangle bits by

$$
 \beta_{ij}=\sum_{t\le j}A_{it},\qquad
 \alpha_{ij}=k_{ij}+\beta_{ij}.
$$

Each prefix sum has only finitely many nonzero terms. Telescoping gives

$$
 \beta_{ij}+\beta_{i,j-1}=A_{ij},\qquad
 \beta_{ij}+\beta_{i-1,j}=B_{ij}.
$$

The resulting labels have finite support. Outside finitely many columns,
and below all input edges, every prefix is zero. Above all input edges,
$B_{ij}=0$, so the second identity makes $\beta_{ij}$ constant across
all columns; that constant is zero because it is zero outside the occupied
columns. Thus $\beta$, and then $\alpha=k+\beta$, vanish outside a
finite box.

Choose the triangles whose labels are one. Their boundary bits are

$$
 \begin{array}{ll}
 \text{horizontal:}&\alpha_{ij}+\beta_{i,j-1}=h_{ij},\\
 \text{vertical:}&\alpha_{ij}+\beta_{i-1,j}=v_{ij},\\
 \text{diagonal:}&\alpha_{ij}+\beta_{ij}=k_{ij}.
 \end{array}
$$

This constructs a finite filling of the given even edge set.

It is unique. The difference of two finite fillings with the same boundary
would have boundary zero. Its diagonal equation gives $\alpha=\beta$;
its horizontal equation gives $\beta_{ij}=\beta_{i,j-1}$.
Each column is constant and finitely supported, so all labels are zero.

### The no holes rule confines the filling to occupied triangles

Now take an even edge subset of $G$. At an unoccupied vertex none of its
six incident edges is selected. Across each of these edges the two
neighbouring triangle labels therefore agree. All six triangles incident
with that vertex have one common label.

Neighbouring unoccupied vertices share incident triangles, so their common
labels agree. From any unoccupied vertex, the no-holes condition supplies
an empty-vertex path beyond a box containing every vertex of every filled
triangle. The common label at its far endpoint is zero, and hence is zero
along the entire path.

Thus no filled triangle touches an unoccupied vertex. Every filling lies
inside $\mathcal T$. Together with uniqueness and the fact that triangle
boundaries are even, this proves a bijection

$$
 \{\text{subsets of }\mathcal T\}
 \longleftrightarrow
 \{\text{even edge subsets of }G\}.
$$

Call this the triangle-filling property. The remaining argument uses this
property; no-holes is the explicit sufficient condition just proved.

### From coloured tile loops to the contact network

The [puzzle rules](https://www.tantrix.com/english/TantrixUnsolved.html)
require matching colours at touching sides, prohibit holes and score the
longest loop of each of four colours. Each tile has three strands with
distinct colours, each joining two sides; see
[Jaap's tile description](https://www.jaapsch.net/puzzles/tantrix.htm).
The formal tile model allows every pairing of six sides into three such
strands, a relaxation containing the actual inventory.

[PhysicalLoops.lean](lean/Tantrix/PhysicalLoops.lean) represents each strand's
two endpoints explicitly and checks their lattice-contact indices.
A placement matches colours across every contact. A selected loop is a
cyclic sequence of distinct strands: enter one endpoint, leave the other,
and cross a genuine contact to the next entry, including the closing step.
Distinct strands express tracing the loop once, not repeatedly scoring
the same circuit. An empty trace contributes zero for a missing colour.

A loop cannot visit a tile twice: that tile has only one strand of the
loop's colour. It cannot reuse a contact: equal exit ports force the same
strand occurrence, while an exit cannot equal any entry port of that
once-traced loop. Two different colours cannot share a contact, because
its matched sides have one colour. Thus departure contacts give a
bijection from all scored tile passages to the selected contacts.
The score is the sum of visited-tile counts over colours, not the number
of tiles in their union.

Around each cyclic trace, the sum of contact incidences at a tile counts
entries and exits equally, hence is zero modulo two. Summing over colours
proves evenness. Neither evenness nor score preservation is an input
assumption. These translation theorems hold for every finite support,
including disconnected supports and supports with holes.
`Loops.score_le_136_of_no_holes` adds only the no-holes and 56-cell
conditions and invokes the geometric upper bound. It bounds every choice
of one loop per colour, so it also bounds the longest loops.

### Counting without a planar Euler theorem

Write $n=|\mathcal V|$, $E=|E(G)|$, and $F=|\mathcal T|$.
A finite connected graph has exactly $2^{E-n+1}$ even edge subsets.
For completeness, choose a spanning tree and choose any subset of the
$E-n+1$ non-tree edges. Correct degrees using tree edges from leaves
toward the root: the current leaf parity uniquely decides whether its
parent edge is selected. At the root the remaining degree is even because
the total degree sum is even. This gives exactly one completion for every
non-tree choice, and all even edge subsets occur.

The filling bijection therefore gives $2^F=2^{E-n+1}$, hence
$F=E-n+1$. No geometric Euler formula is a premise.

Lean uses the equivalent incidence-matrix rank-nullity calculation,
checked in [FiniteGraph.lean](lean/Tantrix/FiniteGraph.lean).

An edge meeting no occupied triangle cannot appear on the boundary of any
subset of $\mathcal T$. By the filling property, it therefore cannot
belong to any even edge subset. This proves the required forced omission
directly, without classifying the edge as a bridge.

Let $b$ count these zero-triangle edges, $P$ the edges in exactly one
triangle, and $I$ those in exactly two triangles. There are no other
possibilities in this lattice. Define

$$
 L:=P+2b.
$$

This is a finite boundary-incidence count; no outer-face definition is
needed. Double counting gives $E=b+P+I$ and $3F=P+2I$.
Together with $F=E-n+1$, these imply

$$
 F=2n-2-L,\qquad E=3n-3-L. \tag{1}
$$

The triangle union has area and perimeter

$$
 A(\mathcal T)=F,\qquad |\partial\mathcal T|=P=L-2b. \tag{2}
$$

These identities include trees, articulation vertices and vertex contacts.

### Maximum even networks and the puzzle score

Choose an even spanning subgraph $H\subseteq G$ with the maximum number
$m$ of edges, and set

$$
 D=E(G)\setminus E(H),\qquad d=|D|,\qquad m=3n-3-L-d. \tag{3}
$$

Every zero-triangle contact is absent from $H$, by the filling argument
above. All $b$ such contacts belong to $D$, so $b\le d$.

Counting physical tile sides gives $6n=2E+S$, so

$$
 S=6+2L,\qquad m=3n-\frac{S+2d}2. \tag{4}
$$

Selected Tantrix loops produce an even subgraph: each colour contributes
degree zero or two at a tile, and distinct colours cannot use the same
tile side. Their total length equals the number of retained contacts.
The maximum $H$ need not be realizable with Tantrix tiles; using it gives
a valid upper bound for actual placements.

### Separated supports

The support need not be connected. Let $D$ be the binary incidence map
from vertex labels to edge labels, and put
$\kappa=\dim\ker D$. Since constants lie in its kernel and the support
is nonempty, $\kappa\ge1$. In graph terms, each component contributes
one independently chosen constant bit. The formal reduction uses only
the dimension and its positivity, not a separate component enumeration.

Rank-nullity and equality of matrix and transpose ranks give
$\dim\ker D^{\mathsf T}+n=E+\kappa$.
The already-checked filling bijection works without connectedness, so
$\dim\ker D^{\mathsf T}=F$. The same triangle-incidence identities then give

$$
 F+L+2\kappa=2n,\qquad E+L+3\kappa=3n.
$$

Set $\delta=\kappa-1\ge0$ and define adjusted budgets
$L'=L+2\delta$, $d'=d+\delta$.
Since $m+d=E$, these satisfy

$$
 F+L'=2n-2,\qquad m+L'+d'=3n-3.
$$

The whole-support and phase-area bounds already allow disconnected
supports. The whole-area bound remains true with $L'$, since
$0\le L\le L'$. The same omission-adjustment identity used in
[Section 3 of the proof](proof.md#3-a-common-budget-for-the-two-phases)
preserves the phase bound: the remainder
$h=(-L-d)\bmod3$ is unchanged, and its numerator increases by

$$
 6\delta(L+2d+2\delta)\ge0.
$$

Thus the connected numerical implication applies to $F,L',d',m$.
These are accounting adjustments, not new edges or a new layout:
the support, no-holes hypothesis and selected score stay unchanged.
There is no need to prove that a geometric joining preserves holes or
fillings.

[Disconnected.lean](lean/Tantrix/Disconnected.lean) proves the kernel
dimension identity, its positivity, the corrected counts and the 136
upper bound without connectedness.

## 2. Directed area bound

For a finite union $R$ of elementary triangles, define $A(R)$ as its
number of triangles. Let $p,q$ count boundary edges incident with upward-
and downward-pointing triangles of $R$. Include all boundary components.
We prove

$$
 p-q\equiv0\pmod3,\qquad
 A(R)\le g(p,q):=\frac{p^2+4pq+q^2}{9}. \tag{5}
$$

If $U,W$ count triangles of the two orientations and $I$ counts shared
edges, then $3U=I+p$, $3W=I+q$. Subtraction gives
$p-q=3(U-W)$.

Use the six lattice directions, indexed in counterclockwise order,

$$
 e_0=(1,0),\ e_1=(0,1),\ e_2=(-1,1),\
 e_3=(-1,0),\ e_4=(0,-1),\ e_5=(1,-1).
$$

The area proof below uses integer coordinates, finite sequences and
determinants. It does not require a convex-hull traversal theorem, a winding
number, or angular rearrangement for arbitrary planar vectors.

### Boundary cancellation gives a closed word

Orient every elementary triangle counterclockwise. If its vertices are
$A,B,C$, then

$$
 \det(A,B)+\det(B,C)+\det(C,A)=1.
$$

Adding over $R$ cancels each internal edge with its reverse. Therefore

$$
 A(R)=\sum_{(A,B)\in\partial R}\det(A,B).
$$

Remaining edges incident with up-triangles have even direction indices;
those incident with down-triangles have odd indices. Incoming and outgoing
boundary incidences balance at every vertex, because they did so for each
triangle before cancellation.

A finite balanced directed edge list decomposes into closed walks.
Initially treat each edge as a one-edge path. Path endpoints remain
balanced: at each vertex, the number of paths ending there equals the
number starting there. If a path is closed, remove it and process the
rest. If a path starts at one vertex and ends at another, balance at its
end supplies a different path starting there. Join those two paths.
Joining preserves endpoint balance and the multiset of edges.

In either case there is one fewer path left to process, so induction on
the number of paths produces closed walks. Their flattened edge list is
a permutation of the original list: every boundary edge occurs exactly
once, with its original orientation. Walks may meet at vertices. Lean
checks this general construction in `ClosedWalks.decompose_edges`.

For a vector word $W=v_1\cdots v_N$, define its displacement and normalized
determinant area by

$$
 \sigma(W)=\sum_i v_i,\qquad
 B(W)=\sum_{i<j}\det(v_i,v_j).
$$

These are algebraic quantities; the word need not trace a simple polygon.
Direct expansion gives

$$
 B(XY)=B(X)+B(Y)+\det(\sigma(X),\sigma(Y)).
$$

For a closed walk starting at $P$, writing each subsequent vertex as
$P$ plus a prefix sum shows that its sum of edge determinants is
$B(W)+\det(P,\sigma(W))=B(W)$. Concatenating the closed boundary words
thus gives a single closed word $W_R$ with

$$
 B(W_R)=A(R).
$$

This derivation includes holes, disconnected regions and vertex pinches:
it is cancellation of oriented edges, not an assertion about the interior
of the concatenated walk. The ordering argument below covers every
closed word, including the empty and zero-area cases. The complete
transfer, including all six direction counts, is checked in
`Grid.BoundaryWalkDecomposition`; `region_boundary_word`
exports the closed word with area and directed counts unchanged.

### Block swap optimality

Among the finitely many permutations of a closed six-direction word,
choose one of maximum $B$. Order the labels as $0<1<\cdots<5$ and
choose the lexicographically least maximizing permutation. We prove this
word is sorted, without a positivity assumption.

Swapping adjacent blocks $U,V$, with any prefix $X$ and suffix $Y$,
changes area by

$$
 B(XVUY)-B(XUVY)=-2\det(\sigma(U),\sigma(V)).
$$

Thus every such pair of blocks in a maximizing word satisfies

$$
 \det(\sigma(U),\sigma(V))\ge0. \tag{6}
$$

If the swap makes the word lexicographically smaller, this determinant
must be strictly positive. Equality would preserve maximum area while
improving the tie-break. This strict form, checked as
`lex_swap_det_pos`, is the only extra principle needed below.
Both forms hold for arbitrary vectors, without closure.

Cyclic rotation preserves $B$ when the word is closed: for $W=XY$,
$\sigma(Y)=-\sigma(X)$, so the cross-term vanishes in either order.

### Grouping equal directions

Suppose a direction $u$ occurs in separated runs. After the last
$u$ of an earlier run, the word contains a segment $uAu$, where
$A$ begins with a direction $v\ne u$. Moving the first $u$
to the right of $A$, or the second $u$ to its left, changes
the area by

$$
 -2\det(u,\sigma(A)),\qquad 2\det(u,\sigma(A)),
$$

respectively. Both changes are nonpositive by maximality, so both are
zero. If $v<u$, the first move makes the word lexicographically
smaller; if $u<v$, the second move does. Both contradict the
tie-break choice. Each direction therefore occurs in one run.

Lean checks this for every lexicographically least maximizer as
`lex_minimum_runGrouped`, and exports the existence consequence as
`exists_grouped_area_maximum`. It holds for any finite word of vectors,
even without closure or noncollinearity. Not every maximizer need have
this property.

### A two swap obstruction

Suppose a maximizing word has the form $tXuvY$, where
$t=u+v$ and $\delta=\det(u,v)>0$. Put $x=\sigma(X)$.

Apply (6) first to the blocks $t$ and $Xu$, then to the blocks
$X$ and $uv$:

$$
 \det(t,x+u)=\det(t,x)-\delta\ge0,
 \qquad
 \det(x,u+v)=-\det(t,x)\ge0.
$$

Adding gives $-\delta\ge0$, a contradiction. Thus consecutive $u,v$
cannot skip an earlier step $u+v$ in this order.

This argument uses only two block swaps. It works for arbitrary vectors
and does not require the word to close. Lean checks it as
`maximum_no_skipped_step`.

### Ordering the six directions

Rotation preserves area, so the least maximizing word starts with its
smallest occurring label: otherwise rotating a smaller label to the front
would improve the lexicographic tie-break.

Suppose consecutive labels descend from $i$ to $j<i$.
Swapping them improves the lexicographic order, so their determinant is
strictly positive by the strict form of (6). Direct inspection of the
six fixed vectors leaves only a transition to label zero or
the transition $5\to1$.

A transition back to zero would return to the initial direction after
leaving its run, contradicting grouping. For $5\to1$, the initial
label is either zero or one.
If it is one, grouping is again contradicted. If it is zero, use

$$
 e_5+e_1=e_0,\qquad \det(e_5,e_1)=1
$$

in the no-skipped-direction lemma. This also gives a contradiction.

There is no descending transition, so the least maximizer is the sorted
word $e_0^a e_1^b e_2^c e_3^d e_4^e e_5^f$, with zero counts allowed.
Lean checks this as `lex_maximum_sorted` and exports
`word_area_le_sorted`: sorting any closed six-direction word cannot
decrease its area. There is no positivity assumption or separate
reversal case. No contraction of runs, count of full turns,
convex-polygon identification or winding theorem is needed.

### The sorted word satisfies the area bound

Write the six direction counts as $a,b,c,d,e,f$. Closure and the directed
counts give

$$
 e=a+b-d,\quad f=c+d-a,\quad p=a+c+e,\quad q=b+d+f.
$$

Its normalized determinant area follows by expanding the six direction
blocks:

$$
 B_{\rm sort}=2(a+b)(c+d)-a^2-d^2.
$$

Put $s=a+b$, $t=c+d$. Completing two squares gives the integer identity

$$
 2(p^2+4pq+q^2)-18B_{\rm sort}
 =9(s-t)^2+3\bigl(3(s+t)-2(p+q)\bigr)^2\ge0.
$$

Hence $A(R)=B(W_R)\le B_{\rm sort}\le g(p,q)$, proving (5).
No equality or rigidity conclusion is needed.

Finally,

$$
 g(p,q)=\frac{(p+q)^2}{6}-\frac{(p-q)^2}{18}
 \le\frac{(p+q)^2}{6}. \tag{7}
$$

## 3. Boundary toggles and the phase counts

For a subset $R$ of the occupied triangles $\mathcal T$, its edge boundary
$\partial R$ is the symmetric difference of their three-edge cycles.
It is therefore an even edge set, including at vertex contacts.
The even graph $H\mathbin{\triangle}\partial R$ has

$$
 m+|\partial R\cap D|-|\partial R\cap H|
$$

edges. The choice of $H$ implies

$$
 |\partial R\cap D|\le|\partial R\cap H|. \tag{8}
$$

This is a consequence of global maximality for any region, with no bound
on $d$. In particular, a phase region cannot be completely enclosed
by omitted contacts: its boundary could simply be added to $H$.

Let $\mathcal B\subseteq\mathcal T$ be the unique finite filling of $H$
constructed in Section 1. Colour triangles in $\mathcal B$ black and
all other lattice triangles white. Across any lattice edge, the two
triangle colours differ exactly when that edge belongs to $H$, by the
definition of the boundary. These are auxiliary binary labels, unrelated
to the physical Tantrix colours.

Label black as 0, white as 1, upward as 0 and downward as 1. A triangle's
phase is the XOR of its auxiliary colour and orientation. A retained
internal edge separates opposite colours and opposite orientations, hence
equal phases. Across an omitted internal edge the colours agree and the
orientations differ, hence the phases differ. Disconnected $H$, isolated
vertices, and pinches require no separate face-colouring argument.

Set $k=d-b$, setting aside the zero-triangle contacts, which are all
omitted. Classify the remaining omitted edges:
$r$ meet exactly one triangle of $\mathcal T$; $a$ meet two black
triangles; and $w$ meet two white triangles. Thus $r+a+w=k$.
Every edge left after this exclusion meets one or two occupied triangles,
and an omitted internal edge has equal colours on both sides.

At an edge meeting only one triangle of $\mathcal T$, the other lattice
triangle is white because it lies outside the filling. The occupied
triangle is therefore black exactly when the edge is retained.

Let $x$ of the $P-r$ retained perimeter incidences, and $y$ of the
$r$ omitted ones, belong to phase 0. Let $R_i$ contain all triangles of
phase $i$. Distinct pieces of one phase share no edge. Internal retained
edges cancel from $\partial R_i$; every internal omitted edge appears
once in each phase boundary. The contributions can be read directly from
the colour and orientation bits:

| Edge class | $(p_0,q_0)$ contribution | $(p_1,q_1)$ contribution |
|---|---|---|
| Retained perimeter edges | $(x,0)$ | $(P-r-x,0)$ |
| Omitted perimeter edges | $(0,y)$ | $(0,r-y)$ |
| Internal omissions between black triangles | $(a,0)$ | $(a,0)$ |
| Internal omissions between white triangles | $(0,w)$ | $(0,w)$ |

Summing gives

$$
 (p_0,q_0)=(x+a,y+w),\qquad
 (p_1,q_1)=(P-r-x+a,r-y+w), \tag{9}
$$

where the second pair is in down/up rather than up/down order. Both
the congruence and $g$ are symmetric under reversal, so this is harmless.
In particular,

$$
 F=A(R_0)+A(R_1)\le g(p_0,q_0)+g(p_1,q_1). \tag{10}
$$

For phase 0 its boundary contains $x$ retained edges and $a+w+y$
omitted edges. For phase 1 those counts are $P-r-x$ and
$a+w+r-y$. Applying (8) yields

$$
 x-y\ge a+w,\qquad P-2r-x+y\ge a+w. \tag{11}
$$

No assertion that the phase regions are connected or convex is used.

## 4. Eliminating the allocation variables

The following calculation maximizes the real bound in (10). It is a
relaxation: some numerical pairs need not be geometric boundaries.

Put $T=P-2k$, $t=x-y-a-w$. Inequalities (11) say $t\ge0$ and
$T-t\ge0$. From (9),

$$
 p_0-q_0=t+2a,\qquad p_1-q_1=T-t+2a.
$$

Both are multiples of three. If $h=a\bmod3\in\{0,1,2\}$, then

$$
 t\equiv T-t\equiv h\pmod3,\quad
 h=(-P-k)\bmod3,\quad h\le t\le T-h. \tag{12}
$$

Thus $k\ge h$ and $T\ge2h$ are necessary. Define

$$
 \Phi(P,k)=
 \frac{P^2+2Pk+4k^2-4(P-2k)h-2h^2}{9},
 \qquad h=(-P-k)\bmod3. \tag{13}
$$

We prove $F\le\Phi(P,k)$.

Set

$$
 t_0=t,\qquad t_1=T-t,\qquad e_i=t_i-h\ge0. \tag{14}
$$

The smaller directed counts in (9) obey

$$
 q_0=y+w\le r+w=k-a,\qquad q_1=r-y+w\le k-a.
$$

Also $p_i=t_i+2a+q_i$. Write
$Q(p,q)=p^2+4pq+q^2=9g(p,q)$, which is increasing in each
coordinate when both are nonnegative. Thus each phase satisfies

$$
 Q(p_i,q_i)\le Q(t_i+k+a,k-a)
 \le (t_i-h)^2+6kt_i+6k^2-3h^2. \tag{15}
$$

The second inequality has the one-product certificate

$$
 (t_i-h)^2+6kt_i+6k^2-3h^2-Q(t_i+k+a,k-a)
 =2(a-h)(t_i+a+h)\ge0.
$$

Now $e_0,e_1\ge0$ and $e_0+e_1=T-2h$, so
$e_0^2+e_1^2\le(T-2h)^2$. Adding (15) gives

$$
\begin{aligned}
 Q(p_0,q_0)+Q(p_1,q_1)
 &\le (T-2h)^2+6kT+12k^2-6h^2\\
 &=P^2+2Pk+4k^2-4(P-2k)h-2h^2.
\end{aligned}
$$

Consequently

$$
 F\le g(p_0,q_0)+g(p_1,q_1)\le\Phi(P,k). \tag{16}
$$

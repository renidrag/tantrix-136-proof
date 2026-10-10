# Proof that 136 is optimal

[Puzzle and overview](README.md) · [Details of the lemmas](technical-details.md) · [Verify in Lean](lean/README.md)

This gives the argument for the Four Longest Loops puzzle under the
[rules in the README](README.md#the-puzzle). It follows Jaap Scherphuis's
perimeter and parity idea, adding the bound that covers every permitted
shape. The supporting derivations are in the linked technical details.

<!-- Adapted from the authoritative proof.md, SHA-256 2bcfde75fcea88e99b31af0e5e80ff2170bbdeadbb24340483316f0afd481feb. Exported 2026-10-09; publication edits only. -->

## 1. The geometric problem

Put a vertex at each tile centre and join centres of touching tiles. The full
contact graph $G$ is induced in the triangular lattice. The selected loops
form an even subgraph: every degree is even, and their total length is its
number of edges. This translation is checked in
[PhysicalLoops.lean](lean/Tantrix/PhysicalLoops.lean): tile sides are paired
into differently coloured strands, and each selected loop is traced once.
Contacts are not repeated within a loop or shared between different colours;
at every tile, entries and exits pair up. The score counts each colour's
visited tiles separately, so a tile shared by two loops contributes twice.
We prove the stronger geometric statement:

> Every even subgraph of the contact graph of a hole-free
> 56-cell support has at most 136 edges, whether connected or not.

Here “no holes” means that every empty hexagonal cell can escape any finite
box through empty side-neighbours. A constructive parity-filling lemma
shows that every even edge subset is the boundary of a unique subset of
the occupied elementary triangles. The no-holes condition is what keeps
the filling inside the support. Details, including separated supports, are in
[technical-details.md](technical-details.md#1-model-and-lattice-filling).

To picture the filling, draw the little triangles whose three corners are
occupied tile centres, and shade some of them. A contact belongs to the
boundary exactly when one of its two neighbouring triangles is shaded and
the other is not.

Now consider a contact beside **no occupied triangle**. Neither of its
neighbouring triangles can be shaded. It cannot appear on the boundary of
any such filling, so it cannot be used by any even network. This gives the
forced omissions directly, without classifying contacts as bridges.

First assume that the support is connected; Section 5 removes this
assumption. Let $F$ count the occupied elementary triangles, $b$ the contacts
meeting no occupied triangle, and $P$ those meeting exactly one.
Define $L=P+2b$.
Counting even edge subsets by triangle fillings and by a spanning tree gives
$F=|E(G)|-55$; counting triangle-edge incidences gives
$3F=2|E(G)|-L$.

Choose a largest even spanning subgraph $H$, and write
$D=E(G)\setminus E(H)$, $d=|D|$. All $b$ contacts identified above
belong to $D$, so $d\ge b$. The two counting identities yield

$$
 F=110-L,\qquad |E(G)|=165-L,\qquad |E(H)|=165-L-d. \tag{1}
$$

If $S$ counts exposed hexagon sides, then $S=6+2L$.
Since $d$ is the minimum number of omitted contacts, the perimeter and
parity accounting in [Jaap's sketch](https://www.jaapsch.net/puzzles/tantrix.htm)
is exactly

$$
 |E(H)|=168-\frac{S+2d}2.
$$

It suffices to prove $L+d\ge29$, equivalently $S+2d\ge64$.
Assume for contradiction that

$$
 c:=L+d\le28. \tag{2}
$$

## 2. Area and maximality

For any finite union $R$ of elementary triangles, let $A(R)$ count its
triangles, and let $p,q$ count boundary edges whose incident triangle in
$R$ points up or down. Include every component and hole boundary. Then

$$
 p-q\equiv0\pmod3,\qquad
 A(R)\le g(p,q):=\frac{p^2+4pq+q^2}{9}
 \le\frac{(p+q)^2}{6}. \tag{3}
$$

The congruence follows by subtracting the edge counts $3U=I+p$,
$3W=I+q$ for up/down triangles. For the area bound, internal oriented
edges cancel, leaving a balanced boundary. Join one-edge paths at matching
endpoints until they form closed walks. Balance ensures an open path
always has a successor, and every join reduces the number of paths.
This keeps each boundary edge exactly once. Concatenating the closed
direction words adds their signed areas without adding any edges.

Choose an area-maximizing permutation, using dictionary order to break
ties between direction sequences. It starts with its smallest direction,
and equal directions form single runs. A swap that improves dictionary
order must strictly lose area; otherwise it contradicts maximality or
the tie-break. Thus a descending pair of labels must have strictly
positive determinant. Checking the six directions leaves only a return
to the initial run or a jump over an earlier direction. Grouping excludes
the first; two block-swap inequalities exclude the second. The word is
therefore sorted, even when its area is zero. An integer two-square
identity gives the bound, with no separate reversal or degenerate case.
The full elementary derivation is in
[technical-details.md](technical-details.md#2-directed-area-bound).

Let $\mathcal T$ be the union of the $F$ occupied triangles. Its perimeter is
$P=L-2b\le L$: only contacts beside exactly one occupied triangle
contribute to this perimeter. Hence $110-L\le L^2/6$.
This is impossible for $L\le22$, so

$$
 23\le L\le28,\qquad 0\le d\le5. \tag{4}
$$

The key observation is that maximality applies to an entire region:

> **Boundary-toggle inequality.** For every subset $R$ of the occupied
> triangles $\mathcal T$,
>
> $$
> |\partial R\cap D|\le|\partial R\cap H|. \tag{5}
> $$

Indeed, $\partial R$ is the symmetric difference of triangle boundaries,
so it is an even edge set. Toggling it preserves even degrees. If more of
its edges were omitted than retained, the toggle would enlarge $H$.
This allows disconnected regions, holes and vertex contacts.

## 3. A common budget for the two phases

Colour the unique filling of $H$ black and all other lattice triangles
white. Give each occupied triangle the phase “auxiliary colour XOR triangle
orientation.” Across a retained internal edge both labels change, so the
phase stays the same; across an omitted edge only orientation changes,
so the phase changes. These labels do not reintroduce physical tile colours.

Write $P=L-2b$ and $k=d-b$, setting aside the $b$ forced omissions
beside no occupied triangle. Each of the remaining omitted contacts
touches one or two occupied triangles. Split them into $r$ perimeter
edges, $a$ internal edges between black triangles, and $w$ internal
edges between white triangles:
$r+a+w=k$.
Let phase 0 receive $x$ retained and $y$ omitted perimeter incidences.
The two phase aggregates have directed perimeter pairs, with coordinates
possibly reversed in one phase,

$$
 (p_0,q_0)=(x+a,y+w),\qquad
 (p_1,q_1)=(P-r-x+a,r-y+w). \tag{6}
$$

By (3), their total area $F$ is at most $g(p_0,q_0)+g(p_1,q_1)$.
Every internal omission borders both phases. Applying (5) to each gives

$$
 x-y\ge a+w,\qquad P-2r-x+y\ge a+w. \tag{7}
$$

Put $T=P-2k$, $t=x-y-a-w$. Then $0\le t\le T$.
The congruences in (3) say

$$
 t\equiv a\pmod3,\qquad T-t\equiv a\pmod3.
$$

Consequently $h:=a\bmod3$ is fixed by
$h=(-P-k)\bmod3$, where $h\in\{0,1,2\}$, and
$h\le t\le T-h$.
The two surpluses are $t_0=t$, $t_1=T-t$. From (6) and
$r+a+w=k$, each phase satisfies

$$
 p_i=t_i+2a+q_i,\qquad 0\le q_i\le k-a,\qquad t_i\ge h,\quad a\ge h.
$$

Write $Q(p,q)=p^2+4pq+q^2=9g(p,q)$. Increasing $q_i$ to its
cap $k-a$ can only increase $Q$. The capped expression obeys

$$
 Q(t_i+k+a,k-a)
 \le (t_i-h)^2+6kt_i+6k^2-3h^2.
$$

The difference is just $2(a-h)(t_i+a+h)\ge0$.
Finally, both $t_i-h$ are nonnegative, so

$$
 (t_0-h)^2+(t_1-h)^2\le(T-2h)^2.
$$

Adding the two phase bounds gives

$$
 F\le \Phi(P,k):=
 \frac{P^2+2Pk+4k^2-4(P-2k)h-2h^2}{9}. \tag{8}
$$

The calculation is written out in
[technical-details.md](technical-details.md#4-eliminating-the-allocation-variables).
The remainder constraints also give $k\ge h$, $P-2k\ge2h$.

To include the $b$ forced omissions in the accounting, replace $(P,k)$
by $(L,d)=(P+2b,k+b)$. This keeps $h$ unchanged and increases $\Phi$
by $2b(P+2k+2b)/3$. Thus (8) holds with $P=L,k=d$. The contacts
themselves remain omitted; only the quantities used in the bound change.

## 4. Two budget cases finish the proof

Recall $c=L+d$, $h=(-c)\bmod3$. Adding $L$ to (8) gives

$$
 9(F+L)\le
 M_h(c,d):=c^2+(9-4h)c+3d^2+(12h-9)d-2h^2. \tag{9}
$$

But $F+L=110$, so the left side is 990. We need only two cases.

If $c\le27$, then $d\le4$. The remainder correction can only lower
the bound, because $c-3d=L-2d\ge0$ and $h\ge0$:

$$
 M_h(c,d)=M_0(c,d)-4(c-3d)h-2h^2\le M_0(c,d)\le984.
$$

The last inequality follows from
$c^2+9c\le27^2+9\cdot27=972$ and
$3d^2-9d\le12$, the latter being equivalent to
$3(4-d)(d+1)\ge0$.

Otherwise $c=28$, so $h=2$ and $d\le5$. Then

$$
 M_2(28,d)=804+3d^2+15d\le804+75+75=954.
$$

Both cases contradict 990. No separate calculation for $h=1$ is needed.

Therefore $L+d\ge29$, and every even subgraph has at most 136 edges.
The four scored loops are such a subgraph, so their score is at most 136.
The published $38+35+33+30=136$ arrangement supplies the matching lower
bound. [ColouredSharpness.lean](lean/Tantrix/ColouredSharpness.lean) checks its
56 distinct inventory tiles, rotations, matching contacts, absence of holes
and four closed loops. The colours score red 33, blue 35, green 38 and
yellow 30. The construction is credited to Milan Kuchtiak; see
[the construction and tile sources](README.md#attribution).

## 5. Disconnected supports

No tiles need to move. For a support with $\kappa\ge1$ components,
the same counting gives $F=2n-2\kappa-L$ and
$m=3n-3\kappa-L-d$. Put $\delta=\kappa-1$ and use the adjusted budgets

$$
 L'=L+2\delta,\qquad d'=d+\delta.
$$

They satisfy $F=2n-2-L'$ and $m=3n-3-L'-d'$, exactly the connected
identities, with the same $F,n,m$. The whole-area estimate is preserved
because $L'\ge L$. The phase estimate is preserved by the same
nonnegative adjustment used for forced omissions in Section 3:
the remainder modulo three is unchanged, and the numerator increases by
$6\delta(L+2d+2\delta)\ge0$.

The same numerical contradiction therefore applies. In Lean, rank-nullity
provides $\delta$ as the dimension of the vertex-incidence kernel minus
one; the constant labellings prove it is nonnegative. No component
enumeration or geometric joining argument is required.
[Disconnected.lean](lean/Tantrix/Disconnected.lean) checks this reduction.

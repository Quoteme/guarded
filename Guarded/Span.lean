/-!
# Source positions

Positions are zero-based `(line, column)` pairs, columns counted in Unicode
scalar values. For every character the language uses (ASCII, `×`, `→`, `▷`)
this coincides with the UTF-16 offsets the LSP protocol expects.
-/

namespace Guarded

structure Pos where
  line : Nat
  col  : Nat
  deriving Inhabited, BEq, Repr

namespace Pos

def le (a b : Pos) : Bool :=
  a.line < b.line || (a.line == b.line && a.col ≤ b.col)

def min (a b : Pos) : Pos := if a.le b then a else b
def max (a b : Pos) : Pos := if a.le b then b else a

instance : ToString Pos := ⟨fun p => s!"{p.line + 1}:{p.col + 1}"⟩

end Pos

/-- A half-open source range `[start, stop)`. -/
structure Span where
  start : Pos
  stop  : Pos
  deriving Inhabited, BEq, Repr

namespace Span

/-- The smallest span covering both arguments. -/
def merge (a b : Span) : Span := ⟨a.start.min b.start, a.stop.max b.stop⟩

/-- Does the span contain `p`? The end position counts as inside, so that a
cursor placed right after an identifier still hovers it. -/
def contains (s : Span) (p : Pos) : Bool := s.start.le p && p.le s.stop

/-- `a` lies inside `b`. -/
def within (a b : Span) : Bool := b.start.le a.start && a.stop.le b.stop

instance : ToString Span := ⟨fun s => s!"{s.start}-{s.stop}"⟩

end Span

/-- Anything that knows where it came from. -/
class HasSpan (α : Type) where
  span : α → Span

export HasSpan (span)

end Guarded

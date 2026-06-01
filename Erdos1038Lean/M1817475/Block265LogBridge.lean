import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block265

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block265

open Set

def block265W1 : Rat := ((5144658707108203 : Rat) / 5000000000000000)
def block265W2 : Rat := ((5394194540149489 : Rat) / 200000000000000000)
def block265W3 : Rat := ((925969538535717 : Rat) / 3125000000000000)
def block265W4 : Rat := (0 : Rat)
def block265S1 : Rat := ((18174751 : Rat) / 10000000)
def block265S2 : Rat := ((511587 : Rat) / 200000)
def block265S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block265S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block265V (y : ℝ) : ℝ :=
  ratPotential block265W1 block265W2 block265W3 block265W4 block265S1 block265S2 block265S3 block265S4 y

def block265LeftParamsCertificate : Bool :=
  allBoxesSameParams block265LeftBoxes block265W1 block265W2 block265W3 block265W4 block265S1 block265S2 block265S3 block265S4

theorem block265LeftParamsCertificate_eq_true :
    block265LeftParamsCertificate = true := by
  native_decide

theorem block265_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block265LeftL : ℝ) (block265LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block265S1 : ℝ))
    (hy2ne : y ≠ (block265S2 : ℝ))
    (hy3ne : y ≠ (block265S3 : ℝ))
    (hy4ne : y ≠ (block265S4 : ℝ)) :
    0 < block265V y := by
  have hcert := block265LeftCertificate_eq_true
  unfold block265LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block265LeftBoxes) (lo := block265LeftL) (hi := block265LeftR)
    (w1 := block265W1) (w2 := block265W2) (w3 := block265W3) (w4 := block265W4)
    (s1 := block265S1) (s2 := block265S2) (s3 := block265S3) (s4 := block265S4)
    hboxes hcover block265LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block265RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block265RightChunk000 block265W1 block265W2 block265W3 block265W4 block265S1 block265S2 block265S3 block265S4

theorem block265RightChunk000ParamsCertificate_eq_true :
    block265RightChunk000ParamsCertificate = true := by
  native_decide

theorem block265_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block265RightChunk000L : ℝ) (block265RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block265S1 : ℝ))
    (hy2ne : y ≠ (block265S2 : ℝ))
    (hy3ne : y ≠ (block265S3 : ℝ))
    (hy4ne : y ≠ (block265S4 : ℝ)) :
    0 < block265V y := by
  have hcert := block265RightChunk000Certificate_eq_true
  unfold block265RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block265RightChunk000) (lo := block265RightChunk000L) (hi := block265RightChunk000R)
    (w1 := block265W1) (w2 := block265W2) (w3 := block265W3) (w4 := block265W4)
    (s1 := block265S1) (s2 := block265S2) (s3 := block265S3) (s4 := block265S4)
    hboxes hcover block265RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block265RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block265RightChunk001 block265W1 block265W2 block265W3 block265W4 block265S1 block265S2 block265S3 block265S4

theorem block265RightChunk001ParamsCertificate_eq_true :
    block265RightChunk001ParamsCertificate = true := by
  native_decide

theorem block265_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block265RightChunk001L : ℝ) (block265RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block265S1 : ℝ))
    (hy2ne : y ≠ (block265S2 : ℝ))
    (hy3ne : y ≠ (block265S3 : ℝ))
    (hy4ne : y ≠ (block265S4 : ℝ)) :
    0 < block265V y := by
  have hcert := block265RightChunk001Certificate_eq_true
  unfold block265RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block265RightChunk001) (lo := block265RightChunk001L) (hi := block265RightChunk001R)
    (w1 := block265W1) (w2 := block265W2) (w3 := block265W3) (w4 := block265W4)
    (s1 := block265S1) (s2 := block265S2) (s3 := block265S3) (s4 := block265S4)
    hboxes hcover block265RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block265_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block265RightL : ℝ) (block265RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block265S1 : ℝ))
    (hy2ne : y ≠ (block265S2 : ℝ))
    (hy3ne : y ≠ (block265S3 : ℝ))
    (hy4ne : y ≠ (block265S4 : ℝ)) :
    0 < block265V y := by
  by_cases h0 : y ≤ (block265RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block265RightChunk000L : ℝ) (block265RightChunk000R : ℝ) := by
      have hL : (block265RightChunk000L : ℝ) = (block265RightL : ℝ) := by
        norm_num [block265RightChunk000L, block265RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block265_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block265RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block265RightChunk001L : ℝ) = (block265RightChunk000R : ℝ) := by
      norm_num [block265RightChunk001L, block265RightChunk000R]
    have hR : (block265RightChunk001R : ℝ) = (block265RightR : ℝ) := by
      norm_num [block265RightChunk001R, block265RightR]
    have hyc : y ∈ Icc (block265RightChunk001L : ℝ) (block265RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block265_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block265_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block265LeftL : ℝ) (block265LeftR : ℝ) →
    y ≠ 0 → y ≠ (block265S1 : ℝ) → y ≠ (block265S2 : ℝ) →
    y ≠ (block265S3 : ℝ) → y ≠ (block265S4 : ℝ) → 0 < block265V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block265RightL : ℝ) (block265RightR : ℝ) →
    y ≠ 0 → y ≠ (block265S1 : ℝ) → y ≠ (block265S2 : ℝ) →
    y ≠ (block265S3 : ℝ) → y ≠ (block265S4 : ℝ) → 0 < block265V y)

theorem block265_reallog_certificate_proof :
    block265_reallog_certificate := by
  exact ⟨block265_left_V_pos, block265_right_V_pos⟩

end Block265
end M1817475
end Erdos1038Lean

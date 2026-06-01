import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block395

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block395

open Set

def block395W1 : Rat := ((1998300862821083 : Rat) / 2500000000000000)
def block395W2 : Rat := ((811657153415767 : Rat) / 20000000000000000)
def block395W3 : Rat := ((17278939343102073 : Rat) / 100000000000000000)
def block395W4 : Rat := ((1461578951266487 : Rat) / 10000000000000000)
def block395S1 : Rat := ((18174751 : Rat) / 10000000)
def block395S2 : Rat := ((511587 : Rat) / 200000)
def block395S3 : Rat := ((132411659910714285773 : Rat) / 50000000000000000000)
def block395S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block395V (y : ℝ) : ℝ :=
  ratPotential block395W1 block395W2 block395W3 block395W4 block395S1 block395S2 block395S3 block395S4 y

def block395LeftParamsCertificate : Bool :=
  allBoxesSameParams block395LeftBoxes block395W1 block395W2 block395W3 block395W4 block395S1 block395S2 block395S3 block395S4

theorem block395LeftParamsCertificate_eq_true :
    block395LeftParamsCertificate = true := by
  native_decide

theorem block395_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block395LeftL : ℝ) (block395LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block395S1 : ℝ))
    (hy2ne : y ≠ (block395S2 : ℝ))
    (hy3ne : y ≠ (block395S3 : ℝ))
    (hy4ne : y ≠ (block395S4 : ℝ)) :
    0 < block395V y := by
  have hcert := block395LeftCertificate_eq_true
  unfold block395LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block395LeftBoxes) (lo := block395LeftL) (hi := block395LeftR)
    (w1 := block395W1) (w2 := block395W2) (w3 := block395W3) (w4 := block395W4)
    (s1 := block395S1) (s2 := block395S2) (s3 := block395S3) (s4 := block395S4)
    hboxes hcover block395LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block395RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block395RightChunk000 block395W1 block395W2 block395W3 block395W4 block395S1 block395S2 block395S3 block395S4

theorem block395RightChunk000ParamsCertificate_eq_true :
    block395RightChunk000ParamsCertificate = true := by
  native_decide

theorem block395_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block395RightChunk000L : ℝ) (block395RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block395S1 : ℝ))
    (hy2ne : y ≠ (block395S2 : ℝ))
    (hy3ne : y ≠ (block395S3 : ℝ))
    (hy4ne : y ≠ (block395S4 : ℝ)) :
    0 < block395V y := by
  have hcert := block395RightChunk000Certificate_eq_true
  unfold block395RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block395RightChunk000) (lo := block395RightChunk000L) (hi := block395RightChunk000R)
    (w1 := block395W1) (w2 := block395W2) (w3 := block395W3) (w4 := block395W4)
    (s1 := block395S1) (s2 := block395S2) (s3 := block395S3) (s4 := block395S4)
    hboxes hcover block395RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block395RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block395RightChunk001 block395W1 block395W2 block395W3 block395W4 block395S1 block395S2 block395S3 block395S4

theorem block395RightChunk001ParamsCertificate_eq_true :
    block395RightChunk001ParamsCertificate = true := by
  native_decide

theorem block395_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block395RightChunk001L : ℝ) (block395RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block395S1 : ℝ))
    (hy2ne : y ≠ (block395S2 : ℝ))
    (hy3ne : y ≠ (block395S3 : ℝ))
    (hy4ne : y ≠ (block395S4 : ℝ)) :
    0 < block395V y := by
  have hcert := block395RightChunk001Certificate_eq_true
  unfold block395RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block395RightChunk001) (lo := block395RightChunk001L) (hi := block395RightChunk001R)
    (w1 := block395W1) (w2 := block395W2) (w3 := block395W3) (w4 := block395W4)
    (s1 := block395S1) (s2 := block395S2) (s3 := block395S3) (s4 := block395S4)
    hboxes hcover block395RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block395_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block395RightL : ℝ) (block395RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block395S1 : ℝ))
    (hy2ne : y ≠ (block395S2 : ℝ))
    (hy3ne : y ≠ (block395S3 : ℝ))
    (hy4ne : y ≠ (block395S4 : ℝ)) :
    0 < block395V y := by
  by_cases h0 : y ≤ (block395RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block395RightChunk000L : ℝ) (block395RightChunk000R : ℝ) := by
      have hL : (block395RightChunk000L : ℝ) = (block395RightL : ℝ) := by
        norm_num [block395RightChunk000L, block395RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block395_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block395RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block395RightChunk001L : ℝ) = (block395RightChunk000R : ℝ) := by
      norm_num [block395RightChunk001L, block395RightChunk000R]
    have hR : (block395RightChunk001R : ℝ) = (block395RightR : ℝ) := by
      norm_num [block395RightChunk001R, block395RightR]
    have hyc : y ∈ Icc (block395RightChunk001L : ℝ) (block395RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block395_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block395_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block395LeftL : ℝ) (block395LeftR : ℝ) →
    y ≠ 0 → y ≠ (block395S1 : ℝ) → y ≠ (block395S2 : ℝ) →
    y ≠ (block395S3 : ℝ) → y ≠ (block395S4 : ℝ) → 0 < block395V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block395RightL : ℝ) (block395RightR : ℝ) →
    y ≠ 0 → y ≠ (block395S1 : ℝ) → y ≠ (block395S2 : ℝ) →
    y ≠ (block395S3 : ℝ) → y ≠ (block395S4 : ℝ) → 0 < block395V y)

theorem block395_reallog_certificate_proof :
    block395_reallog_certificate := by
  exact ⟨block395_left_V_pos, block395_right_V_pos⟩

end Block395
end M1817475
end Erdos1038Lean

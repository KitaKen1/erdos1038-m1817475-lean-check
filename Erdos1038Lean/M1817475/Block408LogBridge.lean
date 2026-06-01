import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block408

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block408

open Set

def block408W1 : Rat := ((3624125036301451 : Rat) / 5000000000000000)
def block408W2 : Rat := (0 : Rat)
def block408W3 : Rat := ((28418393964199257 : Rat) / 100000000000000000)
def block408W4 : Rat := ((4525334616070411 : Rat) / 50000000000000000)
def block408S1 : Rat := ((18174751 : Rat) / 10000000)
def block408S2 : Rat := ((511587 : Rat) / 200000)
def block408S3 : Rat := ((132157521517857142927 : Rat) / 50000000000000000000)
def block408S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block408V (y : ℝ) : ℝ :=
  ratPotential block408W1 block408W2 block408W3 block408W4 block408S1 block408S2 block408S3 block408S4 y

def block408LeftParamsCertificate : Bool :=
  allBoxesSameParams block408LeftBoxes block408W1 block408W2 block408W3 block408W4 block408S1 block408S2 block408S3 block408S4

theorem block408LeftParamsCertificate_eq_true :
    block408LeftParamsCertificate = true := by
  native_decide

theorem block408_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block408LeftL : ℝ) (block408LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block408S1 : ℝ))
    (hy2ne : y ≠ (block408S2 : ℝ))
    (hy3ne : y ≠ (block408S3 : ℝ))
    (hy4ne : y ≠ (block408S4 : ℝ)) :
    0 < block408V y := by
  have hcert := block408LeftCertificate_eq_true
  unfold block408LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block408LeftBoxes) (lo := block408LeftL) (hi := block408LeftR)
    (w1 := block408W1) (w2 := block408W2) (w3 := block408W3) (w4 := block408W4)
    (s1 := block408S1) (s2 := block408S2) (s3 := block408S3) (s4 := block408S4)
    hboxes hcover block408LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block408RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block408RightChunk000 block408W1 block408W2 block408W3 block408W4 block408S1 block408S2 block408S3 block408S4

theorem block408RightChunk000ParamsCertificate_eq_true :
    block408RightChunk000ParamsCertificate = true := by
  native_decide

theorem block408_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block408RightChunk000L : ℝ) (block408RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block408S1 : ℝ))
    (hy2ne : y ≠ (block408S2 : ℝ))
    (hy3ne : y ≠ (block408S3 : ℝ))
    (hy4ne : y ≠ (block408S4 : ℝ)) :
    0 < block408V y := by
  have hcert := block408RightChunk000Certificate_eq_true
  unfold block408RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block408RightChunk000) (lo := block408RightChunk000L) (hi := block408RightChunk000R)
    (w1 := block408W1) (w2 := block408W2) (w3 := block408W3) (w4 := block408W4)
    (s1 := block408S1) (s2 := block408S2) (s3 := block408S3) (s4 := block408S4)
    hboxes hcover block408RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block408RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block408RightChunk001 block408W1 block408W2 block408W3 block408W4 block408S1 block408S2 block408S3 block408S4

theorem block408RightChunk001ParamsCertificate_eq_true :
    block408RightChunk001ParamsCertificate = true := by
  native_decide

theorem block408_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block408RightChunk001L : ℝ) (block408RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block408S1 : ℝ))
    (hy2ne : y ≠ (block408S2 : ℝ))
    (hy3ne : y ≠ (block408S3 : ℝ))
    (hy4ne : y ≠ (block408S4 : ℝ)) :
    0 < block408V y := by
  have hcert := block408RightChunk001Certificate_eq_true
  unfold block408RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block408RightChunk001) (lo := block408RightChunk001L) (hi := block408RightChunk001R)
    (w1 := block408W1) (w2 := block408W2) (w3 := block408W3) (w4 := block408W4)
    (s1 := block408S1) (s2 := block408S2) (s3 := block408S3) (s4 := block408S4)
    hboxes hcover block408RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block408_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block408RightL : ℝ) (block408RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block408S1 : ℝ))
    (hy2ne : y ≠ (block408S2 : ℝ))
    (hy3ne : y ≠ (block408S3 : ℝ))
    (hy4ne : y ≠ (block408S4 : ℝ)) :
    0 < block408V y := by
  by_cases h0 : y ≤ (block408RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block408RightChunk000L : ℝ) (block408RightChunk000R : ℝ) := by
      have hL : (block408RightChunk000L : ℝ) = (block408RightL : ℝ) := by
        norm_num [block408RightChunk000L, block408RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block408_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block408RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block408RightChunk001L : ℝ) = (block408RightChunk000R : ℝ) := by
      norm_num [block408RightChunk001L, block408RightChunk000R]
    have hR : (block408RightChunk001R : ℝ) = (block408RightR : ℝ) := by
      norm_num [block408RightChunk001R, block408RightR]
    have hyc : y ∈ Icc (block408RightChunk001L : ℝ) (block408RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block408_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block408_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block408LeftL : ℝ) (block408LeftR : ℝ) →
    y ≠ 0 → y ≠ (block408S1 : ℝ) → y ≠ (block408S2 : ℝ) →
    y ≠ (block408S3 : ℝ) → y ≠ (block408S4 : ℝ) → 0 < block408V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block408RightL : ℝ) (block408RightR : ℝ) →
    y ≠ 0 → y ≠ (block408S1 : ℝ) → y ≠ (block408S2 : ℝ) →
    y ≠ (block408S3 : ℝ) → y ≠ (block408S4 : ℝ) → 0 < block408V y)

theorem block408_reallog_certificate_proof :
    block408_reallog_certificate := by
  exact ⟨block408_left_V_pos, block408_right_V_pos⟩

end Block408
end M1817475
end Erdos1038Lean

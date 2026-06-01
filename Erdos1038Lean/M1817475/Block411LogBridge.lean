import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block411

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block411

open Set

def block411W1 : Rat := ((715129534312677 : Rat) / 1000000000000000)
def block411W2 : Rat := (0 : Rat)
def block411W3 : Rat := ((179540304732359 : Rat) / 625000000000000)
def block411W4 : Rat := ((2229490332473899 : Rat) / 25000000000000000)
def block411S1 : Rat := ((18174751 : Rat) / 10000000)
def block411S2 : Rat := ((511587 : Rat) / 200000)
def block411S3 : Rat := ((132098874196428571501 : Rat) / 50000000000000000000)
def block411S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block411V (y : ℝ) : ℝ :=
  ratPotential block411W1 block411W2 block411W3 block411W4 block411S1 block411S2 block411S3 block411S4 y

def block411LeftParamsCertificate : Bool :=
  allBoxesSameParams block411LeftBoxes block411W1 block411W2 block411W3 block411W4 block411S1 block411S2 block411S3 block411S4

theorem block411LeftParamsCertificate_eq_true :
    block411LeftParamsCertificate = true := by
  native_decide

theorem block411_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block411LeftL : ℝ) (block411LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block411S1 : ℝ))
    (hy2ne : y ≠ (block411S2 : ℝ))
    (hy3ne : y ≠ (block411S3 : ℝ))
    (hy4ne : y ≠ (block411S4 : ℝ)) :
    0 < block411V y := by
  have hcert := block411LeftCertificate_eq_true
  unfold block411LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block411LeftBoxes) (lo := block411LeftL) (hi := block411LeftR)
    (w1 := block411W1) (w2 := block411W2) (w3 := block411W3) (w4 := block411W4)
    (s1 := block411S1) (s2 := block411S2) (s3 := block411S3) (s4 := block411S4)
    hboxes hcover block411LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block411RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block411RightChunk000 block411W1 block411W2 block411W3 block411W4 block411S1 block411S2 block411S3 block411S4

theorem block411RightChunk000ParamsCertificate_eq_true :
    block411RightChunk000ParamsCertificate = true := by
  native_decide

theorem block411_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block411RightChunk000L : ℝ) (block411RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block411S1 : ℝ))
    (hy2ne : y ≠ (block411S2 : ℝ))
    (hy3ne : y ≠ (block411S3 : ℝ))
    (hy4ne : y ≠ (block411S4 : ℝ)) :
    0 < block411V y := by
  have hcert := block411RightChunk000Certificate_eq_true
  unfold block411RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block411RightChunk000) (lo := block411RightChunk000L) (hi := block411RightChunk000R)
    (w1 := block411W1) (w2 := block411W2) (w3 := block411W3) (w4 := block411W4)
    (s1 := block411S1) (s2 := block411S2) (s3 := block411S3) (s4 := block411S4)
    hboxes hcover block411RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block411RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block411RightChunk001 block411W1 block411W2 block411W3 block411W4 block411S1 block411S2 block411S3 block411S4

theorem block411RightChunk001ParamsCertificate_eq_true :
    block411RightChunk001ParamsCertificate = true := by
  native_decide

theorem block411_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block411RightChunk001L : ℝ) (block411RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block411S1 : ℝ))
    (hy2ne : y ≠ (block411S2 : ℝ))
    (hy3ne : y ≠ (block411S3 : ℝ))
    (hy4ne : y ≠ (block411S4 : ℝ)) :
    0 < block411V y := by
  have hcert := block411RightChunk001Certificate_eq_true
  unfold block411RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block411RightChunk001) (lo := block411RightChunk001L) (hi := block411RightChunk001R)
    (w1 := block411W1) (w2 := block411W2) (w3 := block411W3) (w4 := block411W4)
    (s1 := block411S1) (s2 := block411S2) (s3 := block411S3) (s4 := block411S4)
    hboxes hcover block411RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block411_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block411RightL : ℝ) (block411RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block411S1 : ℝ))
    (hy2ne : y ≠ (block411S2 : ℝ))
    (hy3ne : y ≠ (block411S3 : ℝ))
    (hy4ne : y ≠ (block411S4 : ℝ)) :
    0 < block411V y := by
  by_cases h0 : y ≤ (block411RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block411RightChunk000L : ℝ) (block411RightChunk000R : ℝ) := by
      have hL : (block411RightChunk000L : ℝ) = (block411RightL : ℝ) := by
        norm_num [block411RightChunk000L, block411RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block411_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block411RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block411RightChunk001L : ℝ) = (block411RightChunk000R : ℝ) := by
      norm_num [block411RightChunk001L, block411RightChunk000R]
    have hR : (block411RightChunk001R : ℝ) = (block411RightR : ℝ) := by
      norm_num [block411RightChunk001R, block411RightR]
    have hyc : y ∈ Icc (block411RightChunk001L : ℝ) (block411RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block411_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block411_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block411LeftL : ℝ) (block411LeftR : ℝ) →
    y ≠ 0 → y ≠ (block411S1 : ℝ) → y ≠ (block411S2 : ℝ) →
    y ≠ (block411S3 : ℝ) → y ≠ (block411S4 : ℝ) → 0 < block411V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block411RightL : ℝ) (block411RightR : ℝ) →
    y ≠ 0 → y ≠ (block411S1 : ℝ) → y ≠ (block411S2 : ℝ) →
    y ≠ (block411S3 : ℝ) → y ≠ (block411S4 : ℝ) → 0 < block411V y)

theorem block411_reallog_certificate_proof :
    block411_reallog_certificate := by
  exact ⟨block411_left_V_pos, block411_right_V_pos⟩

end Block411
end M1817475
end Erdos1038Lean

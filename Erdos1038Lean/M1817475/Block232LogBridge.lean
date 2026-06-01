import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block232

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block232

open Set

def block232W1 : Rat := ((8651422829600419 : Rat) / 10000000000000000)
def block232W2 : Rat := ((8348312971082941 : Rat) / 100000000000000000)
def block232W3 : Rat := ((2279193658423111 : Rat) / 12500000000000000)
def block232W4 : Rat := ((7054176564335811 : Rat) / 100000000000000000)
def block232S1 : Rat := ((18174751 : Rat) / 10000000)
def block232S2 : Rat := ((511587 : Rat) / 200000)
def block232S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block232S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block232V (y : ℝ) : ℝ :=
  ratPotential block232W1 block232W2 block232W3 block232W4 block232S1 block232S2 block232S3 block232S4 y

def block232LeftParamsCertificate : Bool :=
  allBoxesSameParams block232LeftBoxes block232W1 block232W2 block232W3 block232W4 block232S1 block232S2 block232S3 block232S4

theorem block232LeftParamsCertificate_eq_true :
    block232LeftParamsCertificate = true := by
  native_decide

theorem block232_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block232LeftL : ℝ) (block232LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block232S1 : ℝ))
    (hy2ne : y ≠ (block232S2 : ℝ))
    (hy3ne : y ≠ (block232S3 : ℝ))
    (hy4ne : y ≠ (block232S4 : ℝ)) :
    0 < block232V y := by
  have hcert := block232LeftCertificate_eq_true
  unfold block232LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block232LeftBoxes) (lo := block232LeftL) (hi := block232LeftR)
    (w1 := block232W1) (w2 := block232W2) (w3 := block232W3) (w4 := block232W4)
    (s1 := block232S1) (s2 := block232S2) (s3 := block232S3) (s4 := block232S4)
    hboxes hcover block232LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block232RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block232RightChunk000 block232W1 block232W2 block232W3 block232W4 block232S1 block232S2 block232S3 block232S4

theorem block232RightChunk000ParamsCertificate_eq_true :
    block232RightChunk000ParamsCertificate = true := by
  native_decide

theorem block232_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block232RightChunk000L : ℝ) (block232RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block232S1 : ℝ))
    (hy2ne : y ≠ (block232S2 : ℝ))
    (hy3ne : y ≠ (block232S3 : ℝ))
    (hy4ne : y ≠ (block232S4 : ℝ)) :
    0 < block232V y := by
  have hcert := block232RightChunk000Certificate_eq_true
  unfold block232RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block232RightChunk000) (lo := block232RightChunk000L) (hi := block232RightChunk000R)
    (w1 := block232W1) (w2 := block232W2) (w3 := block232W3) (w4 := block232W4)
    (s1 := block232S1) (s2 := block232S2) (s3 := block232S3) (s4 := block232S4)
    hboxes hcover block232RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block232RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block232RightChunk001 block232W1 block232W2 block232W3 block232W4 block232S1 block232S2 block232S3 block232S4

theorem block232RightChunk001ParamsCertificate_eq_true :
    block232RightChunk001ParamsCertificate = true := by
  native_decide

theorem block232_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block232RightChunk001L : ℝ) (block232RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block232S1 : ℝ))
    (hy2ne : y ≠ (block232S2 : ℝ))
    (hy3ne : y ≠ (block232S3 : ℝ))
    (hy4ne : y ≠ (block232S4 : ℝ)) :
    0 < block232V y := by
  have hcert := block232RightChunk001Certificate_eq_true
  unfold block232RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block232RightChunk001) (lo := block232RightChunk001L) (hi := block232RightChunk001R)
    (w1 := block232W1) (w2 := block232W2) (w3 := block232W3) (w4 := block232W4)
    (s1 := block232S1) (s2 := block232S2) (s3 := block232S3) (s4 := block232S4)
    hboxes hcover block232RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block232RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block232RightChunk002 block232W1 block232W2 block232W3 block232W4 block232S1 block232S2 block232S3 block232S4

theorem block232RightChunk002ParamsCertificate_eq_true :
    block232RightChunk002ParamsCertificate = true := by
  native_decide

theorem block232_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block232RightChunk002L : ℝ) (block232RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block232S1 : ℝ))
    (hy2ne : y ≠ (block232S2 : ℝ))
    (hy3ne : y ≠ (block232S3 : ℝ))
    (hy4ne : y ≠ (block232S4 : ℝ)) :
    0 < block232V y := by
  have hcert := block232RightChunk002Certificate_eq_true
  unfold block232RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block232RightChunk002) (lo := block232RightChunk002L) (hi := block232RightChunk002R)
    (w1 := block232W1) (w2 := block232W2) (w3 := block232W3) (w4 := block232W4)
    (s1 := block232S1) (s2 := block232S2) (s3 := block232S3) (s4 := block232S4)
    hboxes hcover block232RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block232_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block232RightL : ℝ) (block232RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block232S1 : ℝ))
    (hy2ne : y ≠ (block232S2 : ℝ))
    (hy3ne : y ≠ (block232S3 : ℝ))
    (hy4ne : y ≠ (block232S4 : ℝ)) :
    0 < block232V y := by
  by_cases h0 : y ≤ (block232RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block232RightChunk000L : ℝ) (block232RightChunk000R : ℝ) := by
      have hL : (block232RightChunk000L : ℝ) = (block232RightL : ℝ) := by
        norm_num [block232RightChunk000L, block232RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block232_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block232RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block232RightChunk001L : ℝ) (block232RightChunk001R : ℝ) := by
        have hprev : (block232RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block232RightChunk001L : ℝ) = (block232RightChunk000R : ℝ) := by
          norm_num [block232RightChunk001L, block232RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block232_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block232RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block232RightChunk002L : ℝ) = (block232RightChunk001R : ℝ) := by
        norm_num [block232RightChunk002L, block232RightChunk001R]
      have hR : (block232RightChunk002R : ℝ) = (block232RightR : ℝ) := by
        norm_num [block232RightChunk002R, block232RightR]
      have hyc : y ∈ Icc (block232RightChunk002L : ℝ) (block232RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block232_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block232_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block232LeftL : ℝ) (block232LeftR : ℝ) →
    y ≠ 0 → y ≠ (block232S1 : ℝ) → y ≠ (block232S2 : ℝ) →
    y ≠ (block232S3 : ℝ) → y ≠ (block232S4 : ℝ) → 0 < block232V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block232RightL : ℝ) (block232RightR : ℝ) →
    y ≠ 0 → y ≠ (block232S1 : ℝ) → y ≠ (block232S2 : ℝ) →
    y ≠ (block232S3 : ℝ) → y ≠ (block232S4 : ℝ) → 0 < block232V y)

theorem block232_reallog_certificate_proof :
    block232_reallog_certificate := by
  exact ⟨block232_left_V_pos, block232_right_V_pos⟩

end Block232
end M1817475
end Erdos1038Lean

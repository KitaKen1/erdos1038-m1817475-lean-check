import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block263

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block263

open Set

def block263W1 : Rat := ((10286951410624157 : Rat) / 10000000000000000)
def block263W2 : Rat := ((26176238038646837 : Rat) / 1000000000000000000)
def block263W3 : Rat := ((47616308376409 : Rat) / 160000000000000)
def block263W4 : Rat := (0 : Rat)
def block263S1 : Rat := ((18174751 : Rat) / 10000000)
def block263S2 : Rat := ((511587 : Rat) / 200000)
def block263S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block263S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block263V (y : ℝ) : ℝ :=
  ratPotential block263W1 block263W2 block263W3 block263W4 block263S1 block263S2 block263S3 block263S4 y

def block263LeftParamsCertificate : Bool :=
  allBoxesSameParams block263LeftBoxes block263W1 block263W2 block263W3 block263W4 block263S1 block263S2 block263S3 block263S4

theorem block263LeftParamsCertificate_eq_true :
    block263LeftParamsCertificate = true := by
  native_decide

theorem block263_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block263LeftL : ℝ) (block263LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block263S1 : ℝ))
    (hy2ne : y ≠ (block263S2 : ℝ))
    (hy3ne : y ≠ (block263S3 : ℝ))
    (hy4ne : y ≠ (block263S4 : ℝ)) :
    0 < block263V y := by
  have hcert := block263LeftCertificate_eq_true
  unfold block263LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block263LeftBoxes) (lo := block263LeftL) (hi := block263LeftR)
    (w1 := block263W1) (w2 := block263W2) (w3 := block263W3) (w4 := block263W4)
    (s1 := block263S1) (s2 := block263S2) (s3 := block263S3) (s4 := block263S4)
    hboxes hcover block263LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block263RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block263RightChunk000 block263W1 block263W2 block263W3 block263W4 block263S1 block263S2 block263S3 block263S4

theorem block263RightChunk000ParamsCertificate_eq_true :
    block263RightChunk000ParamsCertificate = true := by
  native_decide

theorem block263_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block263RightChunk000L : ℝ) (block263RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block263S1 : ℝ))
    (hy2ne : y ≠ (block263S2 : ℝ))
    (hy3ne : y ≠ (block263S3 : ℝ))
    (hy4ne : y ≠ (block263S4 : ℝ)) :
    0 < block263V y := by
  have hcert := block263RightChunk000Certificate_eq_true
  unfold block263RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block263RightChunk000) (lo := block263RightChunk000L) (hi := block263RightChunk000R)
    (w1 := block263W1) (w2 := block263W2) (w3 := block263W3) (w4 := block263W4)
    (s1 := block263S1) (s2 := block263S2) (s3 := block263S3) (s4 := block263S4)
    hboxes hcover block263RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block263RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block263RightChunk001 block263W1 block263W2 block263W3 block263W4 block263S1 block263S2 block263S3 block263S4

theorem block263RightChunk001ParamsCertificate_eq_true :
    block263RightChunk001ParamsCertificate = true := by
  native_decide

theorem block263_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block263RightChunk001L : ℝ) (block263RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block263S1 : ℝ))
    (hy2ne : y ≠ (block263S2 : ℝ))
    (hy3ne : y ≠ (block263S3 : ℝ))
    (hy4ne : y ≠ (block263S4 : ℝ)) :
    0 < block263V y := by
  have hcert := block263RightChunk001Certificate_eq_true
  unfold block263RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block263RightChunk001) (lo := block263RightChunk001L) (hi := block263RightChunk001R)
    (w1 := block263W1) (w2 := block263W2) (w3 := block263W3) (w4 := block263W4)
    (s1 := block263S1) (s2 := block263S2) (s3 := block263S3) (s4 := block263S4)
    hboxes hcover block263RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block263RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block263RightChunk002 block263W1 block263W2 block263W3 block263W4 block263S1 block263S2 block263S3 block263S4

theorem block263RightChunk002ParamsCertificate_eq_true :
    block263RightChunk002ParamsCertificate = true := by
  native_decide

theorem block263_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block263RightChunk002L : ℝ) (block263RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block263S1 : ℝ))
    (hy2ne : y ≠ (block263S2 : ℝ))
    (hy3ne : y ≠ (block263S3 : ℝ))
    (hy4ne : y ≠ (block263S4 : ℝ)) :
    0 < block263V y := by
  have hcert := block263RightChunk002Certificate_eq_true
  unfold block263RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block263RightChunk002) (lo := block263RightChunk002L) (hi := block263RightChunk002R)
    (w1 := block263W1) (w2 := block263W2) (w3 := block263W3) (w4 := block263W4)
    (s1 := block263S1) (s2 := block263S2) (s3 := block263S3) (s4 := block263S4)
    hboxes hcover block263RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block263_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block263RightL : ℝ) (block263RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block263S1 : ℝ))
    (hy2ne : y ≠ (block263S2 : ℝ))
    (hy3ne : y ≠ (block263S3 : ℝ))
    (hy4ne : y ≠ (block263S4 : ℝ)) :
    0 < block263V y := by
  by_cases h0 : y ≤ (block263RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block263RightChunk000L : ℝ) (block263RightChunk000R : ℝ) := by
      have hL : (block263RightChunk000L : ℝ) = (block263RightL : ℝ) := by
        norm_num [block263RightChunk000L, block263RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block263_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block263RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block263RightChunk001L : ℝ) (block263RightChunk001R : ℝ) := by
        have hprev : (block263RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block263RightChunk001L : ℝ) = (block263RightChunk000R : ℝ) := by
          norm_num [block263RightChunk001L, block263RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block263_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block263RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block263RightChunk002L : ℝ) = (block263RightChunk001R : ℝ) := by
        norm_num [block263RightChunk002L, block263RightChunk001R]
      have hR : (block263RightChunk002R : ℝ) = (block263RightR : ℝ) := by
        norm_num [block263RightChunk002R, block263RightR]
      have hyc : y ∈ Icc (block263RightChunk002L : ℝ) (block263RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block263_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block263_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block263LeftL : ℝ) (block263LeftR : ℝ) →
    y ≠ 0 → y ≠ (block263S1 : ℝ) → y ≠ (block263S2 : ℝ) →
    y ≠ (block263S3 : ℝ) → y ≠ (block263S4 : ℝ) → 0 < block263V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block263RightL : ℝ) (block263RightR : ℝ) →
    y ≠ 0 → y ≠ (block263S1 : ℝ) → y ≠ (block263S2 : ℝ) →
    y ≠ (block263S3 : ℝ) → y ≠ (block263S4 : ℝ) → 0 < block263V y)

theorem block263_reallog_certificate_proof :
    block263_reallog_certificate := by
  exact ⟨block263_left_V_pos, block263_right_V_pos⟩

end Block263
end M1817475
end Erdos1038Lean

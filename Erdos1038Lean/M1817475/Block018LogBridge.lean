import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block018

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block018

open Set

def block018W1 : Rat := ((34685665603009 : Rat) / 15625000000000)
def block018W2 : Rat := (0 : Rat)
def block018W3 : Rat := (0 : Rat)
def block018W4 : Rat := ((2913735882714621 : Rat) / 10000000000000000)
def block018S1 : Rat := ((18174751 : Rat) / 10000000)
def block018S2 : Rat := ((511587 : Rat) / 200000)
def block018S3 : Rat := ((107000619 : Rat) / 40000000)
def block018S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block018V (y : ℝ) : ℝ :=
  ratPotential block018W1 block018W2 block018W3 block018W4 block018S1 block018S2 block018S3 block018S4 y

def block018LeftParamsCertificate : Bool :=
  allBoxesSameParams block018LeftBoxes block018W1 block018W2 block018W3 block018W4 block018S1 block018S2 block018S3 block018S4

theorem block018LeftParamsCertificate_eq_true :
    block018LeftParamsCertificate = true := by
  native_decide

theorem block018_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block018LeftL : ℝ) (block018LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block018S1 : ℝ))
    (hy2ne : y ≠ (block018S2 : ℝ))
    (hy3ne : y ≠ (block018S3 : ℝ))
    (hy4ne : y ≠ (block018S4 : ℝ)) :
    0 < block018V y := by
  have hcert := block018LeftCertificate_eq_true
  unfold block018LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block018LeftBoxes) (lo := block018LeftL) (hi := block018LeftR)
    (w1 := block018W1) (w2 := block018W2) (w3 := block018W3) (w4 := block018W4)
    (s1 := block018S1) (s2 := block018S2) (s3 := block018S3) (s4 := block018S4)
    hboxes hcover block018LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block018RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block018RightChunk000 block018W1 block018W2 block018W3 block018W4 block018S1 block018S2 block018S3 block018S4

theorem block018RightChunk000ParamsCertificate_eq_true :
    block018RightChunk000ParamsCertificate = true := by
  native_decide

theorem block018_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block018RightChunk000L : ℝ) (block018RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block018S1 : ℝ))
    (hy2ne : y ≠ (block018S2 : ℝ))
    (hy3ne : y ≠ (block018S3 : ℝ))
    (hy4ne : y ≠ (block018S4 : ℝ)) :
    0 < block018V y := by
  have hcert := block018RightChunk000Certificate_eq_true
  unfold block018RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block018RightChunk000) (lo := block018RightChunk000L) (hi := block018RightChunk000R)
    (w1 := block018W1) (w2 := block018W2) (w3 := block018W3) (w4 := block018W4)
    (s1 := block018S1) (s2 := block018S2) (s3 := block018S3) (s4 := block018S4)
    hboxes hcover block018RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block018RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block018RightChunk001 block018W1 block018W2 block018W3 block018W4 block018S1 block018S2 block018S3 block018S4

theorem block018RightChunk001ParamsCertificate_eq_true :
    block018RightChunk001ParamsCertificate = true := by
  native_decide

theorem block018_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block018RightChunk001L : ℝ) (block018RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block018S1 : ℝ))
    (hy2ne : y ≠ (block018S2 : ℝ))
    (hy3ne : y ≠ (block018S3 : ℝ))
    (hy4ne : y ≠ (block018S4 : ℝ)) :
    0 < block018V y := by
  have hcert := block018RightChunk001Certificate_eq_true
  unfold block018RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block018RightChunk001) (lo := block018RightChunk001L) (hi := block018RightChunk001R)
    (w1 := block018W1) (w2 := block018W2) (w3 := block018W3) (w4 := block018W4)
    (s1 := block018S1) (s2 := block018S2) (s3 := block018S3) (s4 := block018S4)
    hboxes hcover block018RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block018RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block018RightChunk002 block018W1 block018W2 block018W3 block018W4 block018S1 block018S2 block018S3 block018S4

theorem block018RightChunk002ParamsCertificate_eq_true :
    block018RightChunk002ParamsCertificate = true := by
  native_decide

theorem block018_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block018RightChunk002L : ℝ) (block018RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block018S1 : ℝ))
    (hy2ne : y ≠ (block018S2 : ℝ))
    (hy3ne : y ≠ (block018S3 : ℝ))
    (hy4ne : y ≠ (block018S4 : ℝ)) :
    0 < block018V y := by
  have hcert := block018RightChunk002Certificate_eq_true
  unfold block018RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block018RightChunk002) (lo := block018RightChunk002L) (hi := block018RightChunk002R)
    (w1 := block018W1) (w2 := block018W2) (w3 := block018W3) (w4 := block018W4)
    (s1 := block018S1) (s2 := block018S2) (s3 := block018S3) (s4 := block018S4)
    hboxes hcover block018RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block018_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block018RightL : ℝ) (block018RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block018S1 : ℝ))
    (hy2ne : y ≠ (block018S2 : ℝ))
    (hy3ne : y ≠ (block018S3 : ℝ))
    (hy4ne : y ≠ (block018S4 : ℝ)) :
    0 < block018V y := by
  by_cases h0 : y ≤ (block018RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block018RightChunk000L : ℝ) (block018RightChunk000R : ℝ) := by
      have hL : (block018RightChunk000L : ℝ) = (block018RightL : ℝ) := by
        norm_num [block018RightChunk000L, block018RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block018_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block018RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block018RightChunk001L : ℝ) (block018RightChunk001R : ℝ) := by
        have hprev : (block018RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block018RightChunk001L : ℝ) = (block018RightChunk000R : ℝ) := by
          norm_num [block018RightChunk001L, block018RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block018_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block018RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block018RightChunk002L : ℝ) = (block018RightChunk001R : ℝ) := by
        norm_num [block018RightChunk002L, block018RightChunk001R]
      have hR : (block018RightChunk002R : ℝ) = (block018RightR : ℝ) := by
        norm_num [block018RightChunk002R, block018RightR]
      have hyc : y ∈ Icc (block018RightChunk002L : ℝ) (block018RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block018_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block018_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block018LeftL : ℝ) (block018LeftR : ℝ) →
    y ≠ 0 → y ≠ (block018S1 : ℝ) → y ≠ (block018S2 : ℝ) →
    y ≠ (block018S3 : ℝ) → y ≠ (block018S4 : ℝ) → 0 < block018V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block018RightL : ℝ) (block018RightR : ℝ) →
    y ≠ 0 → y ≠ (block018S1 : ℝ) → y ≠ (block018S2 : ℝ) →
    y ≠ (block018S3 : ℝ) → y ≠ (block018S4 : ℝ) → 0 < block018V y)

theorem block018_reallog_certificate_proof :
    block018_reallog_certificate := by
  exact ⟨block018_left_V_pos, block018_right_V_pos⟩

end Block018
end M1817475
end Erdos1038Lean

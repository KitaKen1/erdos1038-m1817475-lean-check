import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block403

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block403

open Set

def block403W1 : Rat := ((7409467863375047 : Rat) / 10000000000000000)
def block403W2 : Rat := (0 : Rat)
def block403W3 : Rat := ((5586659077445083 : Rat) / 20000000000000000)
def block403W4 : Rat := ((9249864891533223 : Rat) / 100000000000000000)
def block403S1 : Rat := ((18174751 : Rat) / 10000000)
def block403S2 : Rat := ((511587 : Rat) / 200000)
def block403S3 : Rat := ((132255267053571428637 : Rat) / 50000000000000000000)
def block403S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block403V (y : ℝ) : ℝ :=
  ratPotential block403W1 block403W2 block403W3 block403W4 block403S1 block403S2 block403S3 block403S4 y

def block403LeftParamsCertificate : Bool :=
  allBoxesSameParams block403LeftBoxes block403W1 block403W2 block403W3 block403W4 block403S1 block403S2 block403S3 block403S4

theorem block403LeftParamsCertificate_eq_true :
    block403LeftParamsCertificate = true := by
  native_decide

theorem block403_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block403LeftL : ℝ) (block403LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block403S1 : ℝ))
    (hy2ne : y ≠ (block403S2 : ℝ))
    (hy3ne : y ≠ (block403S3 : ℝ))
    (hy4ne : y ≠ (block403S4 : ℝ)) :
    0 < block403V y := by
  have hcert := block403LeftCertificate_eq_true
  unfold block403LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block403LeftBoxes) (lo := block403LeftL) (hi := block403LeftR)
    (w1 := block403W1) (w2 := block403W2) (w3 := block403W3) (w4 := block403W4)
    (s1 := block403S1) (s2 := block403S2) (s3 := block403S3) (s4 := block403S4)
    hboxes hcover block403LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block403RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block403RightChunk000 block403W1 block403W2 block403W3 block403W4 block403S1 block403S2 block403S3 block403S4

theorem block403RightChunk000ParamsCertificate_eq_true :
    block403RightChunk000ParamsCertificate = true := by
  native_decide

theorem block403_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block403RightChunk000L : ℝ) (block403RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block403S1 : ℝ))
    (hy2ne : y ≠ (block403S2 : ℝ))
    (hy3ne : y ≠ (block403S3 : ℝ))
    (hy4ne : y ≠ (block403S4 : ℝ)) :
    0 < block403V y := by
  have hcert := block403RightChunk000Certificate_eq_true
  unfold block403RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block403RightChunk000) (lo := block403RightChunk000L) (hi := block403RightChunk000R)
    (w1 := block403W1) (w2 := block403W2) (w3 := block403W3) (w4 := block403W4)
    (s1 := block403S1) (s2 := block403S2) (s3 := block403S3) (s4 := block403S4)
    hboxes hcover block403RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block403RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block403RightChunk001 block403W1 block403W2 block403W3 block403W4 block403S1 block403S2 block403S3 block403S4

theorem block403RightChunk001ParamsCertificate_eq_true :
    block403RightChunk001ParamsCertificate = true := by
  native_decide

theorem block403_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block403RightChunk001L : ℝ) (block403RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block403S1 : ℝ))
    (hy2ne : y ≠ (block403S2 : ℝ))
    (hy3ne : y ≠ (block403S3 : ℝ))
    (hy4ne : y ≠ (block403S4 : ℝ)) :
    0 < block403V y := by
  have hcert := block403RightChunk001Certificate_eq_true
  unfold block403RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block403RightChunk001) (lo := block403RightChunk001L) (hi := block403RightChunk001R)
    (w1 := block403W1) (w2 := block403W2) (w3 := block403W3) (w4 := block403W4)
    (s1 := block403S1) (s2 := block403S2) (s3 := block403S3) (s4 := block403S4)
    hboxes hcover block403RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block403RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block403RightChunk002 block403W1 block403W2 block403W3 block403W4 block403S1 block403S2 block403S3 block403S4

theorem block403RightChunk002ParamsCertificate_eq_true :
    block403RightChunk002ParamsCertificate = true := by
  native_decide

theorem block403_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block403RightChunk002L : ℝ) (block403RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block403S1 : ℝ))
    (hy2ne : y ≠ (block403S2 : ℝ))
    (hy3ne : y ≠ (block403S3 : ℝ))
    (hy4ne : y ≠ (block403S4 : ℝ)) :
    0 < block403V y := by
  have hcert := block403RightChunk002Certificate_eq_true
  unfold block403RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block403RightChunk002) (lo := block403RightChunk002L) (hi := block403RightChunk002R)
    (w1 := block403W1) (w2 := block403W2) (w3 := block403W3) (w4 := block403W4)
    (s1 := block403S1) (s2 := block403S2) (s3 := block403S3) (s4 := block403S4)
    hboxes hcover block403RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block403_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block403RightL : ℝ) (block403RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block403S1 : ℝ))
    (hy2ne : y ≠ (block403S2 : ℝ))
    (hy3ne : y ≠ (block403S3 : ℝ))
    (hy4ne : y ≠ (block403S4 : ℝ)) :
    0 < block403V y := by
  by_cases h0 : y ≤ (block403RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block403RightChunk000L : ℝ) (block403RightChunk000R : ℝ) := by
      have hL : (block403RightChunk000L : ℝ) = (block403RightL : ℝ) := by
        norm_num [block403RightChunk000L, block403RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block403_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block403RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block403RightChunk001L : ℝ) (block403RightChunk001R : ℝ) := by
        have hprev : (block403RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block403RightChunk001L : ℝ) = (block403RightChunk000R : ℝ) := by
          norm_num [block403RightChunk001L, block403RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block403_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block403RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block403RightChunk002L : ℝ) = (block403RightChunk001R : ℝ) := by
        norm_num [block403RightChunk002L, block403RightChunk001R]
      have hR : (block403RightChunk002R : ℝ) = (block403RightR : ℝ) := by
        norm_num [block403RightChunk002R, block403RightR]
      have hyc : y ∈ Icc (block403RightChunk002L : ℝ) (block403RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block403_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block403_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block403LeftL : ℝ) (block403LeftR : ℝ) →
    y ≠ 0 → y ≠ (block403S1 : ℝ) → y ≠ (block403S2 : ℝ) →
    y ≠ (block403S3 : ℝ) → y ≠ (block403S4 : ℝ) → 0 < block403V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block403RightL : ℝ) (block403RightR : ℝ) →
    y ≠ 0 → y ≠ (block403S1 : ℝ) → y ≠ (block403S2 : ℝ) →
    y ≠ (block403S3 : ℝ) → y ≠ (block403S4 : ℝ) → 0 < block403V y)

theorem block403_reallog_certificate_proof :
    block403_reallog_certificate := by
  exact ⟨block403_left_V_pos, block403_right_V_pos⟩

end Block403
end M1817475
end Erdos1038Lean

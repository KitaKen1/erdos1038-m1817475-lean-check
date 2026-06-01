import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block221

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block221

open Set

def block221W1 : Rat := ((959272595356271 : Rat) / 1000000000000000)
def block221W2 : Rat := ((5526274615059379 : Rat) / 100000000000000000)
def block221W3 : Rat := ((4309590103677309 : Rat) / 25000000000000000)
def block221W4 : Rat := ((1234581387949497 : Rat) / 12500000000000000)
def block221S1 : Rat := ((18174751 : Rat) / 10000000)
def block221S2 : Rat := ((511587 : Rat) / 200000)
def block221S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block221S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block221V (y : ℝ) : ℝ :=
  ratPotential block221W1 block221W2 block221W3 block221W4 block221S1 block221S2 block221S3 block221S4 y

def block221LeftParamsCertificate : Bool :=
  allBoxesSameParams block221LeftBoxes block221W1 block221W2 block221W3 block221W4 block221S1 block221S2 block221S3 block221S4

theorem block221LeftParamsCertificate_eq_true :
    block221LeftParamsCertificate = true := by
  native_decide

theorem block221_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block221LeftL : ℝ) (block221LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block221S1 : ℝ))
    (hy2ne : y ≠ (block221S2 : ℝ))
    (hy3ne : y ≠ (block221S3 : ℝ))
    (hy4ne : y ≠ (block221S4 : ℝ)) :
    0 < block221V y := by
  have hcert := block221LeftCertificate_eq_true
  unfold block221LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block221LeftBoxes) (lo := block221LeftL) (hi := block221LeftR)
    (w1 := block221W1) (w2 := block221W2) (w3 := block221W3) (w4 := block221W4)
    (s1 := block221S1) (s2 := block221S2) (s3 := block221S3) (s4 := block221S4)
    hboxes hcover block221LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block221RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block221RightChunk000 block221W1 block221W2 block221W3 block221W4 block221S1 block221S2 block221S3 block221S4

theorem block221RightChunk000ParamsCertificate_eq_true :
    block221RightChunk000ParamsCertificate = true := by
  native_decide

theorem block221_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block221RightChunk000L : ℝ) (block221RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block221S1 : ℝ))
    (hy2ne : y ≠ (block221S2 : ℝ))
    (hy3ne : y ≠ (block221S3 : ℝ))
    (hy4ne : y ≠ (block221S4 : ℝ)) :
    0 < block221V y := by
  have hcert := block221RightChunk000Certificate_eq_true
  unfold block221RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block221RightChunk000) (lo := block221RightChunk000L) (hi := block221RightChunk000R)
    (w1 := block221W1) (w2 := block221W2) (w3 := block221W3) (w4 := block221W4)
    (s1 := block221S1) (s2 := block221S2) (s3 := block221S3) (s4 := block221S4)
    hboxes hcover block221RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block221RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block221RightChunk001 block221W1 block221W2 block221W3 block221W4 block221S1 block221S2 block221S3 block221S4

theorem block221RightChunk001ParamsCertificate_eq_true :
    block221RightChunk001ParamsCertificate = true := by
  native_decide

theorem block221_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block221RightChunk001L : ℝ) (block221RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block221S1 : ℝ))
    (hy2ne : y ≠ (block221S2 : ℝ))
    (hy3ne : y ≠ (block221S3 : ℝ))
    (hy4ne : y ≠ (block221S4 : ℝ)) :
    0 < block221V y := by
  have hcert := block221RightChunk001Certificate_eq_true
  unfold block221RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block221RightChunk001) (lo := block221RightChunk001L) (hi := block221RightChunk001R)
    (w1 := block221W1) (w2 := block221W2) (w3 := block221W3) (w4 := block221W4)
    (s1 := block221S1) (s2 := block221S2) (s3 := block221S3) (s4 := block221S4)
    hboxes hcover block221RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block221RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block221RightChunk002 block221W1 block221W2 block221W3 block221W4 block221S1 block221S2 block221S3 block221S4

theorem block221RightChunk002ParamsCertificate_eq_true :
    block221RightChunk002ParamsCertificate = true := by
  native_decide

theorem block221_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block221RightChunk002L : ℝ) (block221RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block221S1 : ℝ))
    (hy2ne : y ≠ (block221S2 : ℝ))
    (hy3ne : y ≠ (block221S3 : ℝ))
    (hy4ne : y ≠ (block221S4 : ℝ)) :
    0 < block221V y := by
  have hcert := block221RightChunk002Certificate_eq_true
  unfold block221RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block221RightChunk002) (lo := block221RightChunk002L) (hi := block221RightChunk002R)
    (w1 := block221W1) (w2 := block221W2) (w3 := block221W3) (w4 := block221W4)
    (s1 := block221S1) (s2 := block221S2) (s3 := block221S3) (s4 := block221S4)
    hboxes hcover block221RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block221_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block221RightL : ℝ) (block221RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block221S1 : ℝ))
    (hy2ne : y ≠ (block221S2 : ℝ))
    (hy3ne : y ≠ (block221S3 : ℝ))
    (hy4ne : y ≠ (block221S4 : ℝ)) :
    0 < block221V y := by
  by_cases h0 : y ≤ (block221RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block221RightChunk000L : ℝ) (block221RightChunk000R : ℝ) := by
      have hL : (block221RightChunk000L : ℝ) = (block221RightL : ℝ) := by
        norm_num [block221RightChunk000L, block221RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block221_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block221RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block221RightChunk001L : ℝ) (block221RightChunk001R : ℝ) := by
        have hprev : (block221RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block221RightChunk001L : ℝ) = (block221RightChunk000R : ℝ) := by
          norm_num [block221RightChunk001L, block221RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block221_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block221RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block221RightChunk002L : ℝ) = (block221RightChunk001R : ℝ) := by
        norm_num [block221RightChunk002L, block221RightChunk001R]
      have hR : (block221RightChunk002R : ℝ) = (block221RightR : ℝ) := by
        norm_num [block221RightChunk002R, block221RightR]
      have hyc : y ∈ Icc (block221RightChunk002L : ℝ) (block221RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block221_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block221_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block221LeftL : ℝ) (block221LeftR : ℝ) →
    y ≠ 0 → y ≠ (block221S1 : ℝ) → y ≠ (block221S2 : ℝ) →
    y ≠ (block221S3 : ℝ) → y ≠ (block221S4 : ℝ) → 0 < block221V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block221RightL : ℝ) (block221RightR : ℝ) →
    y ≠ 0 → y ≠ (block221S1 : ℝ) → y ≠ (block221S2 : ℝ) →
    y ≠ (block221S3 : ℝ) → y ≠ (block221S4 : ℝ) → 0 < block221V y)

theorem block221_reallog_certificate_proof :
    block221_reallog_certificate := by
  exact ⟨block221_left_V_pos, block221_right_V_pos⟩

end Block221
end M1817475
end Erdos1038Lean

import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block227

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block227

open Set

def block227W1 : Rat := ((9554961632827119 : Rat) / 10000000000000000)
def block227W2 : Rat := ((7058861677762123 : Rat) / 125000000000000000)
def block227W3 : Rat := ((3416751329435151 : Rat) / 20000000000000000)
def block227W4 : Rat := ((9952727987603953 : Rat) / 100000000000000000)
def block227S1 : Rat := ((18174751 : Rat) / 10000000)
def block227S2 : Rat := ((511587 : Rat) / 200000)
def block227S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block227S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block227V (y : ℝ) : ℝ :=
  ratPotential block227W1 block227W2 block227W3 block227W4 block227S1 block227S2 block227S3 block227S4 y

def block227LeftParamsCertificate : Bool :=
  allBoxesSameParams block227LeftBoxes block227W1 block227W2 block227W3 block227W4 block227S1 block227S2 block227S3 block227S4

theorem block227LeftParamsCertificate_eq_true :
    block227LeftParamsCertificate = true := by
  native_decide

theorem block227_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block227LeftL : ℝ) (block227LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block227S1 : ℝ))
    (hy2ne : y ≠ (block227S2 : ℝ))
    (hy3ne : y ≠ (block227S3 : ℝ))
    (hy4ne : y ≠ (block227S4 : ℝ)) :
    0 < block227V y := by
  have hcert := block227LeftCertificate_eq_true
  unfold block227LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block227LeftBoxes) (lo := block227LeftL) (hi := block227LeftR)
    (w1 := block227W1) (w2 := block227W2) (w3 := block227W3) (w4 := block227W4)
    (s1 := block227S1) (s2 := block227S2) (s3 := block227S3) (s4 := block227S4)
    hboxes hcover block227LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block227RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block227RightChunk000 block227W1 block227W2 block227W3 block227W4 block227S1 block227S2 block227S3 block227S4

theorem block227RightChunk000ParamsCertificate_eq_true :
    block227RightChunk000ParamsCertificate = true := by
  native_decide

theorem block227_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block227RightChunk000L : ℝ) (block227RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block227S1 : ℝ))
    (hy2ne : y ≠ (block227S2 : ℝ))
    (hy3ne : y ≠ (block227S3 : ℝ))
    (hy4ne : y ≠ (block227S4 : ℝ)) :
    0 < block227V y := by
  have hcert := block227RightChunk000Certificate_eq_true
  unfold block227RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block227RightChunk000) (lo := block227RightChunk000L) (hi := block227RightChunk000R)
    (w1 := block227W1) (w2 := block227W2) (w3 := block227W3) (w4 := block227W4)
    (s1 := block227S1) (s2 := block227S2) (s3 := block227S3) (s4 := block227S4)
    hboxes hcover block227RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block227RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block227RightChunk001 block227W1 block227W2 block227W3 block227W4 block227S1 block227S2 block227S3 block227S4

theorem block227RightChunk001ParamsCertificate_eq_true :
    block227RightChunk001ParamsCertificate = true := by
  native_decide

theorem block227_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block227RightChunk001L : ℝ) (block227RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block227S1 : ℝ))
    (hy2ne : y ≠ (block227S2 : ℝ))
    (hy3ne : y ≠ (block227S3 : ℝ))
    (hy4ne : y ≠ (block227S4 : ℝ)) :
    0 < block227V y := by
  have hcert := block227RightChunk001Certificate_eq_true
  unfold block227RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block227RightChunk001) (lo := block227RightChunk001L) (hi := block227RightChunk001R)
    (w1 := block227W1) (w2 := block227W2) (w3 := block227W3) (w4 := block227W4)
    (s1 := block227S1) (s2 := block227S2) (s3 := block227S3) (s4 := block227S4)
    hboxes hcover block227RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block227RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block227RightChunk002 block227W1 block227W2 block227W3 block227W4 block227S1 block227S2 block227S3 block227S4

theorem block227RightChunk002ParamsCertificate_eq_true :
    block227RightChunk002ParamsCertificate = true := by
  native_decide

theorem block227_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block227RightChunk002L : ℝ) (block227RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block227S1 : ℝ))
    (hy2ne : y ≠ (block227S2 : ℝ))
    (hy3ne : y ≠ (block227S3 : ℝ))
    (hy4ne : y ≠ (block227S4 : ℝ)) :
    0 < block227V y := by
  have hcert := block227RightChunk002Certificate_eq_true
  unfold block227RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block227RightChunk002) (lo := block227RightChunk002L) (hi := block227RightChunk002R)
    (w1 := block227W1) (w2 := block227W2) (w3 := block227W3) (w4 := block227W4)
    (s1 := block227S1) (s2 := block227S2) (s3 := block227S3) (s4 := block227S4)
    hboxes hcover block227RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block227_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block227RightL : ℝ) (block227RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block227S1 : ℝ))
    (hy2ne : y ≠ (block227S2 : ℝ))
    (hy3ne : y ≠ (block227S3 : ℝ))
    (hy4ne : y ≠ (block227S4 : ℝ)) :
    0 < block227V y := by
  by_cases h0 : y ≤ (block227RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block227RightChunk000L : ℝ) (block227RightChunk000R : ℝ) := by
      have hL : (block227RightChunk000L : ℝ) = (block227RightL : ℝ) := by
        norm_num [block227RightChunk000L, block227RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block227_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block227RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block227RightChunk001L : ℝ) (block227RightChunk001R : ℝ) := by
        have hprev : (block227RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block227RightChunk001L : ℝ) = (block227RightChunk000R : ℝ) := by
          norm_num [block227RightChunk001L, block227RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block227_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block227RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block227RightChunk002L : ℝ) = (block227RightChunk001R : ℝ) := by
        norm_num [block227RightChunk002L, block227RightChunk001R]
      have hR : (block227RightChunk002R : ℝ) = (block227RightR : ℝ) := by
        norm_num [block227RightChunk002R, block227RightR]
      have hyc : y ∈ Icc (block227RightChunk002L : ℝ) (block227RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block227_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block227_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block227LeftL : ℝ) (block227LeftR : ℝ) →
    y ≠ 0 → y ≠ (block227S1 : ℝ) → y ≠ (block227S2 : ℝ) →
    y ≠ (block227S3 : ℝ) → y ≠ (block227S4 : ℝ) → 0 < block227V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block227RightL : ℝ) (block227RightR : ℝ) →
    y ≠ 0 → y ≠ (block227S1 : ℝ) → y ≠ (block227S2 : ℝ) →
    y ≠ (block227S3 : ℝ) → y ≠ (block227S4 : ℝ) → 0 < block227V y)

theorem block227_reallog_certificate_proof :
    block227_reallog_certificate := by
  exact ⟨block227_left_V_pos, block227_right_V_pos⟩

end Block227
end M1817475
end Erdos1038Lean

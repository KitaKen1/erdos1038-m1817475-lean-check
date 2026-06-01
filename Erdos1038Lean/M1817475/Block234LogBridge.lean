import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block234

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block234

open Set

def block234W1 : Rat := ((1728200349153623 : Rat) / 2000000000000000)
def block234W2 : Rat := ((8389737035251137 : Rat) / 100000000000000000)
def block234W3 : Rat := ((35517186240389 : Rat) / 195312500000000)
def block234W4 : Rat := ((3538195218030811 : Rat) / 50000000000000000)
def block234S1 : Rat := ((18174751 : Rat) / 10000000)
def block234S2 : Rat := ((511587 : Rat) / 200000)
def block234S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block234S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block234V (y : ℝ) : ℝ :=
  ratPotential block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4 y

def block234LeftParamsCertificate : Bool :=
  allBoxesSameParams block234LeftBoxes block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4

theorem block234LeftParamsCertificate_eq_true :
    block234LeftParamsCertificate = true := by
  native_decide

theorem block234_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234LeftL : ℝ) (block234LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  have hcert := block234LeftCertificate_eq_true
  unfold block234LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block234LeftBoxes) (lo := block234LeftL) (hi := block234LeftR)
    (w1 := block234W1) (w2 := block234W2) (w3 := block234W3) (w4 := block234W4)
    (s1 := block234S1) (s2 := block234S2) (s3 := block234S3) (s4 := block234S4)
    hboxes hcover block234LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block234RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block234RightChunk000 block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4

theorem block234RightChunk000ParamsCertificate_eq_true :
    block234RightChunk000ParamsCertificate = true := by
  native_decide

theorem block234_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234RightChunk000L : ℝ) (block234RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  have hcert := block234RightChunk000Certificate_eq_true
  unfold block234RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block234RightChunk000) (lo := block234RightChunk000L) (hi := block234RightChunk000R)
    (w1 := block234W1) (w2 := block234W2) (w3 := block234W3) (w4 := block234W4)
    (s1 := block234S1) (s2 := block234S2) (s3 := block234S3) (s4 := block234S4)
    hboxes hcover block234RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block234RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block234RightChunk001 block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4

theorem block234RightChunk001ParamsCertificate_eq_true :
    block234RightChunk001ParamsCertificate = true := by
  native_decide

theorem block234_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234RightChunk001L : ℝ) (block234RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  have hcert := block234RightChunk001Certificate_eq_true
  unfold block234RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block234RightChunk001) (lo := block234RightChunk001L) (hi := block234RightChunk001R)
    (w1 := block234W1) (w2 := block234W2) (w3 := block234W3) (w4 := block234W4)
    (s1 := block234S1) (s2 := block234S2) (s3 := block234S3) (s4 := block234S4)
    hboxes hcover block234RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block234RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block234RightChunk002 block234W1 block234W2 block234W3 block234W4 block234S1 block234S2 block234S3 block234S4

theorem block234RightChunk002ParamsCertificate_eq_true :
    block234RightChunk002ParamsCertificate = true := by
  native_decide

theorem block234_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234RightChunk002L : ℝ) (block234RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  have hcert := block234RightChunk002Certificate_eq_true
  unfold block234RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block234RightChunk002) (lo := block234RightChunk002L) (hi := block234RightChunk002R)
    (w1 := block234W1) (w2 := block234W2) (w3 := block234W3) (w4 := block234W4)
    (s1 := block234S1) (s2 := block234S2) (s3 := block234S3) (s4 := block234S4)
    hboxes hcover block234RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block234_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block234RightL : ℝ) (block234RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block234S1 : ℝ))
    (hy2ne : y ≠ (block234S2 : ℝ))
    (hy3ne : y ≠ (block234S3 : ℝ))
    (hy4ne : y ≠ (block234S4 : ℝ)) :
    0 < block234V y := by
  by_cases h0 : y ≤ (block234RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block234RightChunk000L : ℝ) (block234RightChunk000R : ℝ) := by
      have hL : (block234RightChunk000L : ℝ) = (block234RightL : ℝ) := by
        norm_num [block234RightChunk000L, block234RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block234_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block234RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block234RightChunk001L : ℝ) (block234RightChunk001R : ℝ) := by
        have hprev : (block234RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block234RightChunk001L : ℝ) = (block234RightChunk000R : ℝ) := by
          norm_num [block234RightChunk001L, block234RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block234_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block234RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block234RightChunk002L : ℝ) = (block234RightChunk001R : ℝ) := by
        norm_num [block234RightChunk002L, block234RightChunk001R]
      have hR : (block234RightChunk002R : ℝ) = (block234RightR : ℝ) := by
        norm_num [block234RightChunk002R, block234RightR]
      have hyc : y ∈ Icc (block234RightChunk002L : ℝ) (block234RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block234_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block234_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block234LeftL : ℝ) (block234LeftR : ℝ) →
    y ≠ 0 → y ≠ (block234S1 : ℝ) → y ≠ (block234S2 : ℝ) →
    y ≠ (block234S3 : ℝ) → y ≠ (block234S4 : ℝ) → 0 < block234V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block234RightL : ℝ) (block234RightR : ℝ) →
    y ≠ 0 → y ≠ (block234S1 : ℝ) → y ≠ (block234S2 : ℝ) →
    y ≠ (block234S3 : ℝ) → y ≠ (block234S4 : ℝ) → 0 < block234V y)

theorem block234_reallog_certificate_proof :
    block234_reallog_certificate := by
  exact ⟨block234_left_V_pos, block234_right_V_pos⟩

end Block234
end M1817475
end Erdos1038Lean

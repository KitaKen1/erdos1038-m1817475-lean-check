import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block180

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block180

open Set

def block180W1 : Rat := ((17866375234637943 : Rat) / 10000000000000000)
def block180W2 : Rat := (0 : Rat)
def block180W3 : Rat := ((3473946446067867 : Rat) / 20000000000000000)
def block180W4 : Rat := ((484642900889887 : Rat) / 5000000000000000)
def block180S1 : Rat := ((18174751 : Rat) / 10000000)
def block180S2 : Rat := ((511587 : Rat) / 200000)
def block180S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block180S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block180V (y : ℝ) : ℝ :=
  ratPotential block180W1 block180W2 block180W3 block180W4 block180S1 block180S2 block180S3 block180S4 y

def block180LeftParamsCertificate : Bool :=
  allBoxesSameParams block180LeftBoxes block180W1 block180W2 block180W3 block180W4 block180S1 block180S2 block180S3 block180S4

theorem block180LeftParamsCertificate_eq_true :
    block180LeftParamsCertificate = true := by
  native_decide

theorem block180_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block180LeftL : ℝ) (block180LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block180S1 : ℝ))
    (hy2ne : y ≠ (block180S2 : ℝ))
    (hy3ne : y ≠ (block180S3 : ℝ))
    (hy4ne : y ≠ (block180S4 : ℝ)) :
    0 < block180V y := by
  have hcert := block180LeftCertificate_eq_true
  unfold block180LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block180LeftBoxes) (lo := block180LeftL) (hi := block180LeftR)
    (w1 := block180W1) (w2 := block180W2) (w3 := block180W3) (w4 := block180W4)
    (s1 := block180S1) (s2 := block180S2) (s3 := block180S3) (s4 := block180S4)
    hboxes hcover block180LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block180RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block180RightChunk000 block180W1 block180W2 block180W3 block180W4 block180S1 block180S2 block180S3 block180S4

theorem block180RightChunk000ParamsCertificate_eq_true :
    block180RightChunk000ParamsCertificate = true := by
  native_decide

theorem block180_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block180RightChunk000L : ℝ) (block180RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block180S1 : ℝ))
    (hy2ne : y ≠ (block180S2 : ℝ))
    (hy3ne : y ≠ (block180S3 : ℝ))
    (hy4ne : y ≠ (block180S4 : ℝ)) :
    0 < block180V y := by
  have hcert := block180RightChunk000Certificate_eq_true
  unfold block180RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block180RightChunk000) (lo := block180RightChunk000L) (hi := block180RightChunk000R)
    (w1 := block180W1) (w2 := block180W2) (w3 := block180W3) (w4 := block180W4)
    (s1 := block180S1) (s2 := block180S2) (s3 := block180S3) (s4 := block180S4)
    hboxes hcover block180RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block180RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block180RightChunk001 block180W1 block180W2 block180W3 block180W4 block180S1 block180S2 block180S3 block180S4

theorem block180RightChunk001ParamsCertificate_eq_true :
    block180RightChunk001ParamsCertificate = true := by
  native_decide

theorem block180_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block180RightChunk001L : ℝ) (block180RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block180S1 : ℝ))
    (hy2ne : y ≠ (block180S2 : ℝ))
    (hy3ne : y ≠ (block180S3 : ℝ))
    (hy4ne : y ≠ (block180S4 : ℝ)) :
    0 < block180V y := by
  have hcert := block180RightChunk001Certificate_eq_true
  unfold block180RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block180RightChunk001) (lo := block180RightChunk001L) (hi := block180RightChunk001R)
    (w1 := block180W1) (w2 := block180W2) (w3 := block180W3) (w4 := block180W4)
    (s1 := block180S1) (s2 := block180S2) (s3 := block180S3) (s4 := block180S4)
    hboxes hcover block180RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block180_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block180RightL : ℝ) (block180RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block180S1 : ℝ))
    (hy2ne : y ≠ (block180S2 : ℝ))
    (hy3ne : y ≠ (block180S3 : ℝ))
    (hy4ne : y ≠ (block180S4 : ℝ)) :
    0 < block180V y := by
  by_cases h0 : y ≤ (block180RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block180RightChunk000L : ℝ) (block180RightChunk000R : ℝ) := by
      have hL : (block180RightChunk000L : ℝ) = (block180RightL : ℝ) := by
        norm_num [block180RightChunk000L, block180RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block180_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block180RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block180RightChunk001L : ℝ) = (block180RightChunk000R : ℝ) := by
      norm_num [block180RightChunk001L, block180RightChunk000R]
    have hR : (block180RightChunk001R : ℝ) = (block180RightR : ℝ) := by
      norm_num [block180RightChunk001R, block180RightR]
    have hyc : y ∈ Icc (block180RightChunk001L : ℝ) (block180RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block180_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block180_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block180LeftL : ℝ) (block180LeftR : ℝ) →
    y ≠ 0 → y ≠ (block180S1 : ℝ) → y ≠ (block180S2 : ℝ) →
    y ≠ (block180S3 : ℝ) → y ≠ (block180S4 : ℝ) → 0 < block180V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block180RightL : ℝ) (block180RightR : ℝ) →
    y ≠ 0 → y ≠ (block180S1 : ℝ) → y ≠ (block180S2 : ℝ) →
    y ≠ (block180S3 : ℝ) → y ≠ (block180S4 : ℝ) → 0 < block180V y)

theorem block180_reallog_certificate_proof :
    block180_reallog_certificate := by
  exact ⟨block180_left_V_pos, block180_right_V_pos⟩

end Block180
end M1817475
end Erdos1038Lean

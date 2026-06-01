import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block092

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block092

open Set

def block092W1 : Rat := ((116544253509057 : Rat) / 31250000000000)
def block092W2 : Rat := (0 : Rat)
def block092W3 : Rat := (0 : Rat)
def block092W4 : Rat := ((22834335639335027 : Rat) / 100000000000000000)
def block092S1 : Rat := ((18174751 : Rat) / 10000000)
def block092S2 : Rat := ((511587 : Rat) / 200000)
def block092S3 : Rat := ((107000619 : Rat) / 40000000)
def block092S4 : Rat := ((139234303303571423571 : Rat) / 50000000000000000000)

noncomputable def block092V (y : ℝ) : ℝ :=
  ratPotential block092W1 block092W2 block092W3 block092W4 block092S1 block092S2 block092S3 block092S4 y

def block092LeftParamsCertificate : Bool :=
  allBoxesSameParams block092LeftBoxes block092W1 block092W2 block092W3 block092W4 block092S1 block092S2 block092S3 block092S4

theorem block092LeftParamsCertificate_eq_true :
    block092LeftParamsCertificate = true := by
  native_decide

theorem block092_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block092LeftL : ℝ) (block092LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block092S1 : ℝ))
    (hy2ne : y ≠ (block092S2 : ℝ))
    (hy3ne : y ≠ (block092S3 : ℝ))
    (hy4ne : y ≠ (block092S4 : ℝ)) :
    0 < block092V y := by
  have hcert := block092LeftCertificate_eq_true
  unfold block092LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block092LeftBoxes) (lo := block092LeftL) (hi := block092LeftR)
    (w1 := block092W1) (w2 := block092W2) (w3 := block092W3) (w4 := block092W4)
    (s1 := block092S1) (s2 := block092S2) (s3 := block092S3) (s4 := block092S4)
    hboxes hcover block092LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block092RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block092RightChunk000 block092W1 block092W2 block092W3 block092W4 block092S1 block092S2 block092S3 block092S4

theorem block092RightChunk000ParamsCertificate_eq_true :
    block092RightChunk000ParamsCertificate = true := by
  native_decide

theorem block092_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block092RightChunk000L : ℝ) (block092RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block092S1 : ℝ))
    (hy2ne : y ≠ (block092S2 : ℝ))
    (hy3ne : y ≠ (block092S3 : ℝ))
    (hy4ne : y ≠ (block092S4 : ℝ)) :
    0 < block092V y := by
  have hcert := block092RightChunk000Certificate_eq_true
  unfold block092RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block092RightChunk000) (lo := block092RightChunk000L) (hi := block092RightChunk000R)
    (w1 := block092W1) (w2 := block092W2) (w3 := block092W3) (w4 := block092W4)
    (s1 := block092S1) (s2 := block092S2) (s3 := block092S3) (s4 := block092S4)
    hboxes hcover block092RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block092RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block092RightChunk001 block092W1 block092W2 block092W3 block092W4 block092S1 block092S2 block092S3 block092S4

theorem block092RightChunk001ParamsCertificate_eq_true :
    block092RightChunk001ParamsCertificate = true := by
  native_decide

theorem block092_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block092RightChunk001L : ℝ) (block092RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block092S1 : ℝ))
    (hy2ne : y ≠ (block092S2 : ℝ))
    (hy3ne : y ≠ (block092S3 : ℝ))
    (hy4ne : y ≠ (block092S4 : ℝ)) :
    0 < block092V y := by
  have hcert := block092RightChunk001Certificate_eq_true
  unfold block092RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block092RightChunk001) (lo := block092RightChunk001L) (hi := block092RightChunk001R)
    (w1 := block092W1) (w2 := block092W2) (w3 := block092W3) (w4 := block092W4)
    (s1 := block092S1) (s2 := block092S2) (s3 := block092S3) (s4 := block092S4)
    hboxes hcover block092RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block092_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block092RightL : ℝ) (block092RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block092S1 : ℝ))
    (hy2ne : y ≠ (block092S2 : ℝ))
    (hy3ne : y ≠ (block092S3 : ℝ))
    (hy4ne : y ≠ (block092S4 : ℝ)) :
    0 < block092V y := by
  by_cases h0 : y ≤ (block092RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block092RightChunk000L : ℝ) (block092RightChunk000R : ℝ) := by
      have hL : (block092RightChunk000L : ℝ) = (block092RightL : ℝ) := by
        norm_num [block092RightChunk000L, block092RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block092_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block092RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block092RightChunk001L : ℝ) = (block092RightChunk000R : ℝ) := by
      norm_num [block092RightChunk001L, block092RightChunk000R]
    have hR : (block092RightChunk001R : ℝ) = (block092RightR : ℝ) := by
      norm_num [block092RightChunk001R, block092RightR]
    have hyc : y ∈ Icc (block092RightChunk001L : ℝ) (block092RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block092_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block092_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block092LeftL : ℝ) (block092LeftR : ℝ) →
    y ≠ 0 → y ≠ (block092S1 : ℝ) → y ≠ (block092S2 : ℝ) →
    y ≠ (block092S3 : ℝ) → y ≠ (block092S4 : ℝ) → 0 < block092V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block092RightL : ℝ) (block092RightR : ℝ) →
    y ≠ 0 → y ≠ (block092S1 : ℝ) → y ≠ (block092S2 : ℝ) →
    y ≠ (block092S3 : ℝ) → y ≠ (block092S4 : ℝ) → 0 < block092V y)

theorem block092_reallog_certificate_proof :
    block092_reallog_certificate := by
  exact ⟨block092_left_V_pos, block092_right_V_pos⟩

end Block092
end M1817475
end Erdos1038Lean

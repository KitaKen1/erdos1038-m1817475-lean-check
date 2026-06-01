import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block416

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block416

open Set

def block416W1 : Rat := ((6993899391570341 : Rat) / 10000000000000000)
def block416W2 : Rat := (0 : Rat)
def block416W3 : Rat := ((2923986340962117 : Rat) / 10000000000000000)
def block416W4 : Rat := ((347814631447751 : Rat) / 4000000000000000)
def block416S1 : Rat := ((18174751 : Rat) / 10000000)
def block416S2 : Rat := ((511587 : Rat) / 200000)
def block416S3 : Rat := ((132001128660714285791 : Rat) / 50000000000000000000)
def block416S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block416V (y : ℝ) : ℝ :=
  ratPotential block416W1 block416W2 block416W3 block416W4 block416S1 block416S2 block416S3 block416S4 y

def block416LeftParamsCertificate : Bool :=
  allBoxesSameParams block416LeftBoxes block416W1 block416W2 block416W3 block416W4 block416S1 block416S2 block416S3 block416S4

theorem block416LeftParamsCertificate_eq_true :
    block416LeftParamsCertificate = true := by
  native_decide

theorem block416_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block416LeftL : ℝ) (block416LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block416S1 : ℝ))
    (hy2ne : y ≠ (block416S2 : ℝ))
    (hy3ne : y ≠ (block416S3 : ℝ))
    (hy4ne : y ≠ (block416S4 : ℝ)) :
    0 < block416V y := by
  have hcert := block416LeftCertificate_eq_true
  unfold block416LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block416LeftBoxes) (lo := block416LeftL) (hi := block416LeftR)
    (w1 := block416W1) (w2 := block416W2) (w3 := block416W3) (w4 := block416W4)
    (s1 := block416S1) (s2 := block416S2) (s3 := block416S3) (s4 := block416S4)
    hboxes hcover block416LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block416RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block416RightChunk000 block416W1 block416W2 block416W3 block416W4 block416S1 block416S2 block416S3 block416S4

theorem block416RightChunk000ParamsCertificate_eq_true :
    block416RightChunk000ParamsCertificate = true := by
  native_decide

theorem block416_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block416RightChunk000L : ℝ) (block416RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block416S1 : ℝ))
    (hy2ne : y ≠ (block416S2 : ℝ))
    (hy3ne : y ≠ (block416S3 : ℝ))
    (hy4ne : y ≠ (block416S4 : ℝ)) :
    0 < block416V y := by
  have hcert := block416RightChunk000Certificate_eq_true
  unfold block416RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block416RightChunk000) (lo := block416RightChunk000L) (hi := block416RightChunk000R)
    (w1 := block416W1) (w2 := block416W2) (w3 := block416W3) (w4 := block416W4)
    (s1 := block416S1) (s2 := block416S2) (s3 := block416S3) (s4 := block416S4)
    hboxes hcover block416RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block416RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block416RightChunk001 block416W1 block416W2 block416W3 block416W4 block416S1 block416S2 block416S3 block416S4

theorem block416RightChunk001ParamsCertificate_eq_true :
    block416RightChunk001ParamsCertificate = true := by
  native_decide

theorem block416_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block416RightChunk001L : ℝ) (block416RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block416S1 : ℝ))
    (hy2ne : y ≠ (block416S2 : ℝ))
    (hy3ne : y ≠ (block416S3 : ℝ))
    (hy4ne : y ≠ (block416S4 : ℝ)) :
    0 < block416V y := by
  have hcert := block416RightChunk001Certificate_eq_true
  unfold block416RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block416RightChunk001) (lo := block416RightChunk001L) (hi := block416RightChunk001R)
    (w1 := block416W1) (w2 := block416W2) (w3 := block416W3) (w4 := block416W4)
    (s1 := block416S1) (s2 := block416S2) (s3 := block416S3) (s4 := block416S4)
    hboxes hcover block416RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block416_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block416RightL : ℝ) (block416RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block416S1 : ℝ))
    (hy2ne : y ≠ (block416S2 : ℝ))
    (hy3ne : y ≠ (block416S3 : ℝ))
    (hy4ne : y ≠ (block416S4 : ℝ)) :
    0 < block416V y := by
  by_cases h0 : y ≤ (block416RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block416RightChunk000L : ℝ) (block416RightChunk000R : ℝ) := by
      have hL : (block416RightChunk000L : ℝ) = (block416RightL : ℝ) := by
        norm_num [block416RightChunk000L, block416RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block416_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block416RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block416RightChunk001L : ℝ) = (block416RightChunk000R : ℝ) := by
      norm_num [block416RightChunk001L, block416RightChunk000R]
    have hR : (block416RightChunk001R : ℝ) = (block416RightR : ℝ) := by
      norm_num [block416RightChunk001R, block416RightR]
    have hyc : y ∈ Icc (block416RightChunk001L : ℝ) (block416RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block416_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block416_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block416LeftL : ℝ) (block416LeftR : ℝ) →
    y ≠ 0 → y ≠ (block416S1 : ℝ) → y ≠ (block416S2 : ℝ) →
    y ≠ (block416S3 : ℝ) → y ≠ (block416S4 : ℝ) → 0 < block416V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block416RightL : ℝ) (block416RightR : ℝ) →
    y ≠ 0 → y ≠ (block416S1 : ℝ) → y ≠ (block416S2 : ℝ) →
    y ≠ (block416S3 : ℝ) → y ≠ (block416S4 : ℝ) → 0 < block416V y)

theorem block416_reallog_certificate_proof :
    block416_reallog_certificate := by
  exact ⟨block416_left_V_pos, block416_right_V_pos⟩

end Block416
end M1817475
end Erdos1038Lean

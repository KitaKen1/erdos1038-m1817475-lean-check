import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block393

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block393

open Set

def block393W1 : Rat := ((50123610034503 : Rat) / 62500000000000)
def block393W2 : Rat := ((4092803739623337 : Rat) / 100000000000000000)
def block393W3 : Rat := ((17210002328261223 : Rat) / 100000000000000000)
def block393W4 : Rat := ((2918805832577957 : Rat) / 20000000000000000)
def block393S1 : Rat := ((18174751 : Rat) / 10000000)
def block393S2 : Rat := ((511587 : Rat) / 200000)
def block393S3 : Rat := ((132450758125000000057 : Rat) / 50000000000000000000)
def block393S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block393V (y : ℝ) : ℝ :=
  ratPotential block393W1 block393W2 block393W3 block393W4 block393S1 block393S2 block393S3 block393S4 y

def block393LeftParamsCertificate : Bool :=
  allBoxesSameParams block393LeftBoxes block393W1 block393W2 block393W3 block393W4 block393S1 block393S2 block393S3 block393S4

theorem block393LeftParamsCertificate_eq_true :
    block393LeftParamsCertificate = true := by
  native_decide

theorem block393_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block393LeftL : ℝ) (block393LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block393S1 : ℝ))
    (hy2ne : y ≠ (block393S2 : ℝ))
    (hy3ne : y ≠ (block393S3 : ℝ))
    (hy4ne : y ≠ (block393S4 : ℝ)) :
    0 < block393V y := by
  have hcert := block393LeftCertificate_eq_true
  unfold block393LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block393LeftBoxes) (lo := block393LeftL) (hi := block393LeftR)
    (w1 := block393W1) (w2 := block393W2) (w3 := block393W3) (w4 := block393W4)
    (s1 := block393S1) (s2 := block393S2) (s3 := block393S3) (s4 := block393S4)
    hboxes hcover block393LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block393RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block393RightChunk000 block393W1 block393W2 block393W3 block393W4 block393S1 block393S2 block393S3 block393S4

theorem block393RightChunk000ParamsCertificate_eq_true :
    block393RightChunk000ParamsCertificate = true := by
  native_decide

theorem block393_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block393RightChunk000L : ℝ) (block393RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block393S1 : ℝ))
    (hy2ne : y ≠ (block393S2 : ℝ))
    (hy3ne : y ≠ (block393S3 : ℝ))
    (hy4ne : y ≠ (block393S4 : ℝ)) :
    0 < block393V y := by
  have hcert := block393RightChunk000Certificate_eq_true
  unfold block393RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block393RightChunk000) (lo := block393RightChunk000L) (hi := block393RightChunk000R)
    (w1 := block393W1) (w2 := block393W2) (w3 := block393W3) (w4 := block393W4)
    (s1 := block393S1) (s2 := block393S2) (s3 := block393S3) (s4 := block393S4)
    hboxes hcover block393RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block393RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block393RightChunk001 block393W1 block393W2 block393W3 block393W4 block393S1 block393S2 block393S3 block393S4

theorem block393RightChunk001ParamsCertificate_eq_true :
    block393RightChunk001ParamsCertificate = true := by
  native_decide

theorem block393_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block393RightChunk001L : ℝ) (block393RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block393S1 : ℝ))
    (hy2ne : y ≠ (block393S2 : ℝ))
    (hy3ne : y ≠ (block393S3 : ℝ))
    (hy4ne : y ≠ (block393S4 : ℝ)) :
    0 < block393V y := by
  have hcert := block393RightChunk001Certificate_eq_true
  unfold block393RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block393RightChunk001) (lo := block393RightChunk001L) (hi := block393RightChunk001R)
    (w1 := block393W1) (w2 := block393W2) (w3 := block393W3) (w4 := block393W4)
    (s1 := block393S1) (s2 := block393S2) (s3 := block393S3) (s4 := block393S4)
    hboxes hcover block393RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block393_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block393RightL : ℝ) (block393RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block393S1 : ℝ))
    (hy2ne : y ≠ (block393S2 : ℝ))
    (hy3ne : y ≠ (block393S3 : ℝ))
    (hy4ne : y ≠ (block393S4 : ℝ)) :
    0 < block393V y := by
  by_cases h0 : y ≤ (block393RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block393RightChunk000L : ℝ) (block393RightChunk000R : ℝ) := by
      have hL : (block393RightChunk000L : ℝ) = (block393RightL : ℝ) := by
        norm_num [block393RightChunk000L, block393RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block393_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block393RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block393RightChunk001L : ℝ) = (block393RightChunk000R : ℝ) := by
      norm_num [block393RightChunk001L, block393RightChunk000R]
    have hR : (block393RightChunk001R : ℝ) = (block393RightR : ℝ) := by
      norm_num [block393RightChunk001R, block393RightR]
    have hyc : y ∈ Icc (block393RightChunk001L : ℝ) (block393RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block393_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block393_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block393LeftL : ℝ) (block393LeftR : ℝ) →
    y ≠ 0 → y ≠ (block393S1 : ℝ) → y ≠ (block393S2 : ℝ) →
    y ≠ (block393S3 : ℝ) → y ≠ (block393S4 : ℝ) → 0 < block393V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block393RightL : ℝ) (block393RightR : ℝ) →
    y ≠ 0 → y ≠ (block393S1 : ℝ) → y ≠ (block393S2 : ℝ) →
    y ≠ (block393S3 : ℝ) → y ≠ (block393S4 : ℝ) → 0 < block393V y)

theorem block393_reallog_certificate_proof :
    block393_reallog_certificate := by
  exact ⟨block393_left_V_pos, block393_right_V_pos⟩

end Block393
end M1817475
end Erdos1038Lean

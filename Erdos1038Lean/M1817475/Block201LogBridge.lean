import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block201

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block201

open Set

def block201W1 : Rat := ((9724008168480401 : Rat) / 10000000000000000)
def block201W2 : Rat := ((2497457054639 : Rat) / 48828125000000)
def block201W3 : Rat := ((17771782270978131 : Rat) / 100000000000000000)
def block201W4 : Rat := ((4808090340703939 : Rat) / 50000000000000000)
def block201S1 : Rat := ((18174751 : Rat) / 10000000)
def block201S2 : Rat := ((511587 : Rat) / 200000)
def block201S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block201S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block201V (y : ℝ) : ℝ :=
  ratPotential block201W1 block201W2 block201W3 block201W4 block201S1 block201S2 block201S3 block201S4 y

def block201LeftParamsCertificate : Bool :=
  allBoxesSameParams block201LeftBoxes block201W1 block201W2 block201W3 block201W4 block201S1 block201S2 block201S3 block201S4

theorem block201LeftParamsCertificate_eq_true :
    block201LeftParamsCertificate = true := by
  native_decide

theorem block201_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block201LeftL : ℝ) (block201LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block201S1 : ℝ))
    (hy2ne : y ≠ (block201S2 : ℝ))
    (hy3ne : y ≠ (block201S3 : ℝ))
    (hy4ne : y ≠ (block201S4 : ℝ)) :
    0 < block201V y := by
  have hcert := block201LeftCertificate_eq_true
  unfold block201LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block201LeftBoxes) (lo := block201LeftL) (hi := block201LeftR)
    (w1 := block201W1) (w2 := block201W2) (w3 := block201W3) (w4 := block201W4)
    (s1 := block201S1) (s2 := block201S2) (s3 := block201S3) (s4 := block201S4)
    hboxes hcover block201LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block201RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block201RightChunk000 block201W1 block201W2 block201W3 block201W4 block201S1 block201S2 block201S3 block201S4

theorem block201RightChunk000ParamsCertificate_eq_true :
    block201RightChunk000ParamsCertificate = true := by
  native_decide

theorem block201_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block201RightChunk000L : ℝ) (block201RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block201S1 : ℝ))
    (hy2ne : y ≠ (block201S2 : ℝ))
    (hy3ne : y ≠ (block201S3 : ℝ))
    (hy4ne : y ≠ (block201S4 : ℝ)) :
    0 < block201V y := by
  have hcert := block201RightChunk000Certificate_eq_true
  unfold block201RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block201RightChunk000) (lo := block201RightChunk000L) (hi := block201RightChunk000R)
    (w1 := block201W1) (w2 := block201W2) (w3 := block201W3) (w4 := block201W4)
    (s1 := block201S1) (s2 := block201S2) (s3 := block201S3) (s4 := block201S4)
    hboxes hcover block201RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block201RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block201RightChunk001 block201W1 block201W2 block201W3 block201W4 block201S1 block201S2 block201S3 block201S4

theorem block201RightChunk001ParamsCertificate_eq_true :
    block201RightChunk001ParamsCertificate = true := by
  native_decide

theorem block201_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block201RightChunk001L : ℝ) (block201RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block201S1 : ℝ))
    (hy2ne : y ≠ (block201S2 : ℝ))
    (hy3ne : y ≠ (block201S3 : ℝ))
    (hy4ne : y ≠ (block201S4 : ℝ)) :
    0 < block201V y := by
  have hcert := block201RightChunk001Certificate_eq_true
  unfold block201RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block201RightChunk001) (lo := block201RightChunk001L) (hi := block201RightChunk001R)
    (w1 := block201W1) (w2 := block201W2) (w3 := block201W3) (w4 := block201W4)
    (s1 := block201S1) (s2 := block201S2) (s3 := block201S3) (s4 := block201S4)
    hboxes hcover block201RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block201RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block201RightChunk002 block201W1 block201W2 block201W3 block201W4 block201S1 block201S2 block201S3 block201S4

theorem block201RightChunk002ParamsCertificate_eq_true :
    block201RightChunk002ParamsCertificate = true := by
  native_decide

theorem block201_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block201RightChunk002L : ℝ) (block201RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block201S1 : ℝ))
    (hy2ne : y ≠ (block201S2 : ℝ))
    (hy3ne : y ≠ (block201S3 : ℝ))
    (hy4ne : y ≠ (block201S4 : ℝ)) :
    0 < block201V y := by
  have hcert := block201RightChunk002Certificate_eq_true
  unfold block201RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block201RightChunk002) (lo := block201RightChunk002L) (hi := block201RightChunk002R)
    (w1 := block201W1) (w2 := block201W2) (w3 := block201W3) (w4 := block201W4)
    (s1 := block201S1) (s2 := block201S2) (s3 := block201S3) (s4 := block201S4)
    hboxes hcover block201RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block201RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block201RightChunk003 block201W1 block201W2 block201W3 block201W4 block201S1 block201S2 block201S3 block201S4

theorem block201RightChunk003ParamsCertificate_eq_true :
    block201RightChunk003ParamsCertificate = true := by
  native_decide

theorem block201_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block201RightChunk003L : ℝ) (block201RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block201S1 : ℝ))
    (hy2ne : y ≠ (block201S2 : ℝ))
    (hy3ne : y ≠ (block201S3 : ℝ))
    (hy4ne : y ≠ (block201S4 : ℝ)) :
    0 < block201V y := by
  have hcert := block201RightChunk003Certificate_eq_true
  unfold block201RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block201RightChunk003) (lo := block201RightChunk003L) (hi := block201RightChunk003R)
    (w1 := block201W1) (w2 := block201W2) (w3 := block201W3) (w4 := block201W4)
    (s1 := block201S1) (s2 := block201S2) (s3 := block201S3) (s4 := block201S4)
    hboxes hcover block201RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block201RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block201RightChunk004 block201W1 block201W2 block201W3 block201W4 block201S1 block201S2 block201S3 block201S4

theorem block201RightChunk004ParamsCertificate_eq_true :
    block201RightChunk004ParamsCertificate = true := by
  native_decide

theorem block201_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block201RightChunk004L : ℝ) (block201RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block201S1 : ℝ))
    (hy2ne : y ≠ (block201S2 : ℝ))
    (hy3ne : y ≠ (block201S3 : ℝ))
    (hy4ne : y ≠ (block201S4 : ℝ)) :
    0 < block201V y := by
  have hcert := block201RightChunk004Certificate_eq_true
  unfold block201RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block201RightChunk004) (lo := block201RightChunk004L) (hi := block201RightChunk004R)
    (w1 := block201W1) (w2 := block201W2) (w3 := block201W3) (w4 := block201W4)
    (s1 := block201S1) (s2 := block201S2) (s3 := block201S3) (s4 := block201S4)
    hboxes hcover block201RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block201RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block201RightChunk005 block201W1 block201W2 block201W3 block201W4 block201S1 block201S2 block201S3 block201S4

theorem block201RightChunk005ParamsCertificate_eq_true :
    block201RightChunk005ParamsCertificate = true := by
  native_decide

theorem block201_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block201RightChunk005L : ℝ) (block201RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block201S1 : ℝ))
    (hy2ne : y ≠ (block201S2 : ℝ))
    (hy3ne : y ≠ (block201S3 : ℝ))
    (hy4ne : y ≠ (block201S4 : ℝ)) :
    0 < block201V y := by
  have hcert := block201RightChunk005Certificate_eq_true
  unfold block201RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block201RightChunk005) (lo := block201RightChunk005L) (hi := block201RightChunk005R)
    (w1 := block201W1) (w2 := block201W2) (w3 := block201W3) (w4 := block201W4)
    (s1 := block201S1) (s2 := block201S2) (s3 := block201S3) (s4 := block201S4)
    hboxes hcover block201RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block201RightChunk006ParamsCertificate : Bool :=
  allBoxesSameParams block201RightChunk006 block201W1 block201W2 block201W3 block201W4 block201S1 block201S2 block201S3 block201S4

theorem block201RightChunk006ParamsCertificate_eq_true :
    block201RightChunk006ParamsCertificate = true := by
  native_decide

theorem block201_right_chunk006_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block201RightChunk006L : ℝ) (block201RightChunk006R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block201S1 : ℝ))
    (hy2ne : y ≠ (block201S2 : ℝ))
    (hy3ne : y ≠ (block201S3 : ℝ))
    (hy4ne : y ≠ (block201S4 : ℝ)) :
    0 < block201V y := by
  have hcert := block201RightChunk006Certificate_eq_true
  unfold block201RightChunk006Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block201RightChunk006) (lo := block201RightChunk006L) (hi := block201RightChunk006R)
    (w1 := block201W1) (w2 := block201W2) (w3 := block201W3) (w4 := block201W4)
    (s1 := block201S1) (s2 := block201S2) (s3 := block201S3) (s4 := block201S4)
    hboxes hcover block201RightChunk006ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block201_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block201RightL : ℝ) (block201RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block201S1 : ℝ))
    (hy2ne : y ≠ (block201S2 : ℝ))
    (hy3ne : y ≠ (block201S3 : ℝ))
    (hy4ne : y ≠ (block201S4 : ℝ)) :
    0 < block201V y := by
  by_cases h0 : y ≤ (block201RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block201RightChunk000L : ℝ) (block201RightChunk000R : ℝ) := by
      have hL : (block201RightChunk000L : ℝ) = (block201RightL : ℝ) := by
        norm_num [block201RightChunk000L, block201RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block201_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block201RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block201RightChunk001L : ℝ) (block201RightChunk001R : ℝ) := by
        have hprev : (block201RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block201RightChunk001L : ℝ) = (block201RightChunk000R : ℝ) := by
          norm_num [block201RightChunk001L, block201RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block201_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block201RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block201RightChunk002L : ℝ) (block201RightChunk002R : ℝ) := by
          have hprev : (block201RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block201RightChunk002L : ℝ) = (block201RightChunk001R : ℝ) := by
            norm_num [block201RightChunk002L, block201RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block201_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block201RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block201RightChunk003L : ℝ) (block201RightChunk003R : ℝ) := by
            have hprev : (block201RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block201RightChunk003L : ℝ) = (block201RightChunk002R : ℝ) := by
              norm_num [block201RightChunk003L, block201RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block201_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block201RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block201RightChunk004L : ℝ) (block201RightChunk004R : ℝ) := by
              have hprev : (block201RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block201RightChunk004L : ℝ) = (block201RightChunk003R : ℝ) := by
                norm_num [block201RightChunk004L, block201RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block201_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            by_cases h5 : y ≤ (block201RightChunk005R : ℝ)
            · have hyc : y ∈ Icc (block201RightChunk005L : ℝ) (block201RightChunk005R : ℝ) := by
                have hprev : (block201RightChunk004R : ℝ) < y := lt_of_not_ge h4
                have hL : (block201RightChunk005L : ℝ) = (block201RightChunk004R : ℝ) := by
                  norm_num [block201RightChunk005L, block201RightChunk004R]
                constructor
                · linarith [hprev, hL]
                · exact h5
              exact block201_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
            ·
              have hprev : (block201RightChunk005R : ℝ) < y := lt_of_not_ge h5
              have hL : (block201RightChunk006L : ℝ) = (block201RightChunk005R : ℝ) := by
                norm_num [block201RightChunk006L, block201RightChunk005R]
              have hR : (block201RightChunk006R : ℝ) = (block201RightR : ℝ) := by
                norm_num [block201RightChunk006R, block201RightR]
              have hyc : y ∈ Icc (block201RightChunk006L : ℝ) (block201RightChunk006R : ℝ) := by
                constructor
                · linarith [hprev, hL]
                · linarith [hy.2, hR]
              exact block201_right_chunk006_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block201_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block201LeftL : ℝ) (block201LeftR : ℝ) →
    y ≠ 0 → y ≠ (block201S1 : ℝ) → y ≠ (block201S2 : ℝ) →
    y ≠ (block201S3 : ℝ) → y ≠ (block201S4 : ℝ) → 0 < block201V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block201RightL : ℝ) (block201RightR : ℝ) →
    y ≠ 0 → y ≠ (block201S1 : ℝ) → y ≠ (block201S2 : ℝ) →
    y ≠ (block201S3 : ℝ) → y ≠ (block201S4 : ℝ) → 0 < block201V y)

theorem block201_reallog_certificate_proof :
    block201_reallog_certificate := by
  exact ⟨block201_left_V_pos, block201_right_V_pos⟩

end Block201
end M1817475
end Erdos1038Lean

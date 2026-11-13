/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Compose named parse/image chunk lemmas for lines 50–99 via
`parseDecText_append` and `extract_split`. Group results are
combined through named prefix definitions so Lean does not
reduce a long concatenation in a theorem type.
-/

import IntFmt.ParseJoinCore
import IntFmt.DecBindDataB

namespace IntFmt

set_option maxHeartbeats 800000
set_option maxRecDepth 20000

@[irreducible] def text_050_054 : String := decLine050 ++ decLine051 ++ decLine052 ++ decLine053 ++ decLine054
@[irreducible] def image_050_054 : Array UInt16 := ((((decChunk050 ++ decChunk051) ++ decChunk052) ++ decChunk053) ++ decChunk054)
private theorem ws_050_054_0 : listEndsWS decLine050.toList :=
  decLine050_ws
private theorem ws_050_054_1 : listEndsWS (decLine050 ++ decLine051).toList :=
  ws_cat (decLine050) decLine051 ws_050_054_0 decLine051_ws
private theorem ws_050_054_2 : listEndsWS (decLine050 ++ decLine051 ++ decLine052).toList :=
  ws_cat (decLine050 ++ decLine051) decLine052 ws_050_054_1 decLine052_ws
private theorem ws_050_054_3 : listEndsWS (decLine050 ++ decLine051 ++ decLine052 ++ decLine053).toList :=
  ws_cat (decLine050 ++ decLine051 ++ decLine052) decLine053 ws_050_054_2 decLine053_ws
private theorem ws_050_054_4 : listEndsWS (decLine050 ++ decLine051 ++ decLine052 ++ decLine053 ++ decLine054).toList :=
  ws_cat (decLine050 ++ decLine051 ++ decLine052 ++ decLine053) decLine054 ws_050_054_3 decLine054_ws
theorem parse_050_054 : parseDecText text_050_054 = image_050_054 := by
  have p1 := parse_append_eq decLine050 decLine051
    decChunk050 decChunk051
    ws_050_054_0 parse_line050 parse_line051
  have p2 := parse_append_eq (decLine050 ++ decLine051) decLine052
    (decChunk050 ++ decChunk051) decChunk052
    ws_050_054_1 p1 parse_line052
  have p3 := parse_append_eq (decLine050 ++ decLine051 ++ decLine052) decLine053
    ((decChunk050 ++ decChunk051) ++ decChunk052) decChunk053
    ws_050_054_2 p2 parse_line053
  have p4 := parse_append_eq (decLine050 ++ decLine051 ++ decLine052 ++ decLine053) decLine054
    (((decChunk050 ++ decChunk051) ++ decChunk052) ++ decChunk053) decChunk054
    ws_050_054_3 p3 parse_line054
  rw [text_050_054, image_050_054]
  exact p4
theorem extract_050_054 :
    intfmtImage.extract 800 880 = image_050_054 := by
  have i1 := extract_append_eq 800 816 832
    decChunk050 decChunk051
    (by decide) (by decide) (by decide)
    image_chunk050 image_chunk051
  have i2 := extract_append_eq 800 832 848
    (decChunk050 ++ decChunk051) decChunk052
    (by decide) (by decide) (by decide)
    i1 image_chunk052
  have i3 := extract_append_eq 800 848 864
    ((decChunk050 ++ decChunk051) ++ decChunk052) decChunk053
    (by decide) (by decide) (by decide)
    i2 image_chunk053
  have i4 := extract_append_eq 800 864 880
    (((decChunk050 ++ decChunk051) ++ decChunk052) ++ decChunk053) decChunk054
    (by decide) (by decide) (by decide)
    i3 image_chunk054
  rw [image_050_054]
  exact i4
private theorem ws_text_050_054 : listEndsWS text_050_054.toList := by
  unfold text_050_054
  exact ws_050_054_4

@[irreducible] def text_055_059 : String := decLine055 ++ decLine056 ++ decLine057 ++ decLine058 ++ decLine059
@[irreducible] def image_055_059 : Array UInt16 := ((((decChunk055 ++ decChunk056) ++ decChunk057) ++ decChunk058) ++ decChunk059)
private theorem ws_055_059_0 : listEndsWS decLine055.toList :=
  decLine055_ws
private theorem ws_055_059_1 : listEndsWS (decLine055 ++ decLine056).toList :=
  ws_cat (decLine055) decLine056 ws_055_059_0 decLine056_ws
private theorem ws_055_059_2 : listEndsWS (decLine055 ++ decLine056 ++ decLine057).toList :=
  ws_cat (decLine055 ++ decLine056) decLine057 ws_055_059_1 decLine057_ws
private theorem ws_055_059_3 : listEndsWS (decLine055 ++ decLine056 ++ decLine057 ++ decLine058).toList :=
  ws_cat (decLine055 ++ decLine056 ++ decLine057) decLine058 ws_055_059_2 decLine058_ws
private theorem ws_055_059_4 : listEndsWS (decLine055 ++ decLine056 ++ decLine057 ++ decLine058 ++ decLine059).toList :=
  ws_cat (decLine055 ++ decLine056 ++ decLine057 ++ decLine058) decLine059 ws_055_059_3 decLine059_ws
theorem parse_055_059 : parseDecText text_055_059 = image_055_059 := by
  have p1 := parse_append_eq decLine055 decLine056
    decChunk055 decChunk056
    ws_055_059_0 parse_line055 parse_line056
  have p2 := parse_append_eq (decLine055 ++ decLine056) decLine057
    (decChunk055 ++ decChunk056) decChunk057
    ws_055_059_1 p1 parse_line057
  have p3 := parse_append_eq (decLine055 ++ decLine056 ++ decLine057) decLine058
    ((decChunk055 ++ decChunk056) ++ decChunk057) decChunk058
    ws_055_059_2 p2 parse_line058
  have p4 := parse_append_eq (decLine055 ++ decLine056 ++ decLine057 ++ decLine058) decLine059
    (((decChunk055 ++ decChunk056) ++ decChunk057) ++ decChunk058) decChunk059
    ws_055_059_3 p3 parse_line059
  rw [text_055_059, image_055_059]
  exact p4
theorem extract_055_059 :
    intfmtImage.extract 880 960 = image_055_059 := by
  have i1 := extract_append_eq 880 896 912
    decChunk055 decChunk056
    (by decide) (by decide) (by decide)
    image_chunk055 image_chunk056
  have i2 := extract_append_eq 880 912 928
    (decChunk055 ++ decChunk056) decChunk057
    (by decide) (by decide) (by decide)
    i1 image_chunk057
  have i3 := extract_append_eq 880 928 944
    ((decChunk055 ++ decChunk056) ++ decChunk057) decChunk058
    (by decide) (by decide) (by decide)
    i2 image_chunk058
  have i4 := extract_append_eq 880 944 960
    (((decChunk055 ++ decChunk056) ++ decChunk057) ++ decChunk058) decChunk059
    (by decide) (by decide) (by decide)
    i3 image_chunk059
  rw [image_055_059]
  exact i4
private theorem ws_text_055_059 : listEndsWS text_055_059.toList := by
  unfold text_055_059
  exact ws_055_059_4

@[irreducible] def text_060_064 : String := decLine060 ++ decLine061 ++ decLine062 ++ decLine063 ++ decLine064
@[irreducible] def image_060_064 : Array UInt16 := ((((decChunk060 ++ decChunk061) ++ decChunk062) ++ decChunk063) ++ decChunk064)
private theorem ws_060_064_0 : listEndsWS decLine060.toList :=
  decLine060_ws
private theorem ws_060_064_1 : listEndsWS (decLine060 ++ decLine061).toList :=
  ws_cat (decLine060) decLine061 ws_060_064_0 decLine061_ws
private theorem ws_060_064_2 : listEndsWS (decLine060 ++ decLine061 ++ decLine062).toList :=
  ws_cat (decLine060 ++ decLine061) decLine062 ws_060_064_1 decLine062_ws
private theorem ws_060_064_3 : listEndsWS (decLine060 ++ decLine061 ++ decLine062 ++ decLine063).toList :=
  ws_cat (decLine060 ++ decLine061 ++ decLine062) decLine063 ws_060_064_2 decLine063_ws
private theorem ws_060_064_4 : listEndsWS (decLine060 ++ decLine061 ++ decLine062 ++ decLine063 ++ decLine064).toList :=
  ws_cat (decLine060 ++ decLine061 ++ decLine062 ++ decLine063) decLine064 ws_060_064_3 decLine064_ws
theorem parse_060_064 : parseDecText text_060_064 = image_060_064 := by
  have p1 := parse_append_eq decLine060 decLine061
    decChunk060 decChunk061
    ws_060_064_0 parse_line060 parse_line061
  have p2 := parse_append_eq (decLine060 ++ decLine061) decLine062
    (decChunk060 ++ decChunk061) decChunk062
    ws_060_064_1 p1 parse_line062
  have p3 := parse_append_eq (decLine060 ++ decLine061 ++ decLine062) decLine063
    ((decChunk060 ++ decChunk061) ++ decChunk062) decChunk063
    ws_060_064_2 p2 parse_line063
  have p4 := parse_append_eq (decLine060 ++ decLine061 ++ decLine062 ++ decLine063) decLine064
    (((decChunk060 ++ decChunk061) ++ decChunk062) ++ decChunk063) decChunk064
    ws_060_064_3 p3 parse_line064
  rw [text_060_064, image_060_064]
  exact p4
theorem extract_060_064 :
    intfmtImage.extract 960 1040 = image_060_064 := by
  have i1 := extract_append_eq 960 976 992
    decChunk060 decChunk061
    (by decide) (by decide) (by decide)
    image_chunk060 image_chunk061
  have i2 := extract_append_eq 960 992 1008
    (decChunk060 ++ decChunk061) decChunk062
    (by decide) (by decide) (by decide)
    i1 image_chunk062
  have i3 := extract_append_eq 960 1008 1024
    ((decChunk060 ++ decChunk061) ++ decChunk062) decChunk063
    (by decide) (by decide) (by decide)
    i2 image_chunk063
  have i4 := extract_append_eq 960 1024 1040
    (((decChunk060 ++ decChunk061) ++ decChunk062) ++ decChunk063) decChunk064
    (by decide) (by decide) (by decide)
    i3 image_chunk064
  rw [image_060_064]
  exact i4
private theorem ws_text_060_064 : listEndsWS text_060_064.toList := by
  unfold text_060_064
  exact ws_060_064_4

@[irreducible] def text_065_069 : String := decLine065 ++ decLine066 ++ decLine067 ++ decLine068 ++ decLine069
@[irreducible] def image_065_069 : Array UInt16 := ((((decChunk065 ++ decChunk066) ++ decChunk067) ++ decChunk068) ++ decChunk069)
private theorem ws_065_069_0 : listEndsWS decLine065.toList :=
  decLine065_ws
private theorem ws_065_069_1 : listEndsWS (decLine065 ++ decLine066).toList :=
  ws_cat (decLine065) decLine066 ws_065_069_0 decLine066_ws
private theorem ws_065_069_2 : listEndsWS (decLine065 ++ decLine066 ++ decLine067).toList :=
  ws_cat (decLine065 ++ decLine066) decLine067 ws_065_069_1 decLine067_ws
private theorem ws_065_069_3 : listEndsWS (decLine065 ++ decLine066 ++ decLine067 ++ decLine068).toList :=
  ws_cat (decLine065 ++ decLine066 ++ decLine067) decLine068 ws_065_069_2 decLine068_ws
private theorem ws_065_069_4 : listEndsWS (decLine065 ++ decLine066 ++ decLine067 ++ decLine068 ++ decLine069).toList :=
  ws_cat (decLine065 ++ decLine066 ++ decLine067 ++ decLine068) decLine069 ws_065_069_3 decLine069_ws
theorem parse_065_069 : parseDecText text_065_069 = image_065_069 := by
  have p1 := parse_append_eq decLine065 decLine066
    decChunk065 decChunk066
    ws_065_069_0 parse_line065 parse_line066
  have p2 := parse_append_eq (decLine065 ++ decLine066) decLine067
    (decChunk065 ++ decChunk066) decChunk067
    ws_065_069_1 p1 parse_line067
  have p3 := parse_append_eq (decLine065 ++ decLine066 ++ decLine067) decLine068
    ((decChunk065 ++ decChunk066) ++ decChunk067) decChunk068
    ws_065_069_2 p2 parse_line068
  have p4 := parse_append_eq (decLine065 ++ decLine066 ++ decLine067 ++ decLine068) decLine069
    (((decChunk065 ++ decChunk066) ++ decChunk067) ++ decChunk068) decChunk069
    ws_065_069_3 p3 parse_line069
  rw [text_065_069, image_065_069]
  exact p4
theorem extract_065_069 :
    intfmtImage.extract 1040 1120 = image_065_069 := by
  have i1 := extract_append_eq 1040 1056 1072
    decChunk065 decChunk066
    (by decide) (by decide) (by decide)
    image_chunk065 image_chunk066
  have i2 := extract_append_eq 1040 1072 1088
    (decChunk065 ++ decChunk066) decChunk067
    (by decide) (by decide) (by decide)
    i1 image_chunk067
  have i3 := extract_append_eq 1040 1088 1104
    ((decChunk065 ++ decChunk066) ++ decChunk067) decChunk068
    (by decide) (by decide) (by decide)
    i2 image_chunk068
  have i4 := extract_append_eq 1040 1104 1120
    (((decChunk065 ++ decChunk066) ++ decChunk067) ++ decChunk068) decChunk069
    (by decide) (by decide) (by decide)
    i3 image_chunk069
  rw [image_065_069]
  exact i4
private theorem ws_text_065_069 : listEndsWS text_065_069.toList := by
  unfold text_065_069
  exact ws_065_069_4

@[irreducible] def text_070_074 : String := decLine070 ++ decLine071 ++ decLine072 ++ decLine073 ++ decLine074
@[irreducible] def image_070_074 : Array UInt16 := ((((decChunk070 ++ decChunk071) ++ decChunk072) ++ decChunk073) ++ decChunk074)
private theorem ws_070_074_0 : listEndsWS decLine070.toList :=
  decLine070_ws
private theorem ws_070_074_1 : listEndsWS (decLine070 ++ decLine071).toList :=
  ws_cat (decLine070) decLine071 ws_070_074_0 decLine071_ws
private theorem ws_070_074_2 : listEndsWS (decLine070 ++ decLine071 ++ decLine072).toList :=
  ws_cat (decLine070 ++ decLine071) decLine072 ws_070_074_1 decLine072_ws
private theorem ws_070_074_3 : listEndsWS (decLine070 ++ decLine071 ++ decLine072 ++ decLine073).toList :=
  ws_cat (decLine070 ++ decLine071 ++ decLine072) decLine073 ws_070_074_2 decLine073_ws
private theorem ws_070_074_4 : listEndsWS (decLine070 ++ decLine071 ++ decLine072 ++ decLine073 ++ decLine074).toList :=
  ws_cat (decLine070 ++ decLine071 ++ decLine072 ++ decLine073) decLine074 ws_070_074_3 decLine074_ws
theorem parse_070_074 : parseDecText text_070_074 = image_070_074 := by
  have p1 := parse_append_eq decLine070 decLine071
    decChunk070 decChunk071
    ws_070_074_0 parse_line070 parse_line071
  have p2 := parse_append_eq (decLine070 ++ decLine071) decLine072
    (decChunk070 ++ decChunk071) decChunk072
    ws_070_074_1 p1 parse_line072
  have p3 := parse_append_eq (decLine070 ++ decLine071 ++ decLine072) decLine073
    ((decChunk070 ++ decChunk071) ++ decChunk072) decChunk073
    ws_070_074_2 p2 parse_line073
  have p4 := parse_append_eq (decLine070 ++ decLine071 ++ decLine072 ++ decLine073) decLine074
    (((decChunk070 ++ decChunk071) ++ decChunk072) ++ decChunk073) decChunk074
    ws_070_074_3 p3 parse_line074
  rw [text_070_074, image_070_074]
  exact p4
theorem extract_070_074 :
    intfmtImage.extract 1120 1200 = image_070_074 := by
  have i1 := extract_append_eq 1120 1136 1152
    decChunk070 decChunk071
    (by decide) (by decide) (by decide)
    image_chunk070 image_chunk071
  have i2 := extract_append_eq 1120 1152 1168
    (decChunk070 ++ decChunk071) decChunk072
    (by decide) (by decide) (by decide)
    i1 image_chunk072
  have i3 := extract_append_eq 1120 1168 1184
    ((decChunk070 ++ decChunk071) ++ decChunk072) decChunk073
    (by decide) (by decide) (by decide)
    i2 image_chunk073
  have i4 := extract_append_eq 1120 1184 1200
    (((decChunk070 ++ decChunk071) ++ decChunk072) ++ decChunk073) decChunk074
    (by decide) (by decide) (by decide)
    i3 image_chunk074
  rw [image_070_074]
  exact i4
private theorem ws_text_070_074 : listEndsWS text_070_074.toList := by
  unfold text_070_074
  exact ws_070_074_4

@[irreducible] def text_075_079 : String := decLine075 ++ decLine076 ++ decLine077 ++ decLine078 ++ decLine079
@[irreducible] def image_075_079 : Array UInt16 := ((((decChunk075 ++ decChunk076) ++ decChunk077) ++ decChunk078) ++ decChunk079)
private theorem ws_075_079_0 : listEndsWS decLine075.toList :=
  decLine075_ws
private theorem ws_075_079_1 : listEndsWS (decLine075 ++ decLine076).toList :=
  ws_cat (decLine075) decLine076 ws_075_079_0 decLine076_ws
private theorem ws_075_079_2 : listEndsWS (decLine075 ++ decLine076 ++ decLine077).toList :=
  ws_cat (decLine075 ++ decLine076) decLine077 ws_075_079_1 decLine077_ws
private theorem ws_075_079_3 : listEndsWS (decLine075 ++ decLine076 ++ decLine077 ++ decLine078).toList :=
  ws_cat (decLine075 ++ decLine076 ++ decLine077) decLine078 ws_075_079_2 decLine078_ws
private theorem ws_075_079_4 : listEndsWS (decLine075 ++ decLine076 ++ decLine077 ++ decLine078 ++ decLine079).toList :=
  ws_cat (decLine075 ++ decLine076 ++ decLine077 ++ decLine078) decLine079 ws_075_079_3 decLine079_ws
theorem parse_075_079 : parseDecText text_075_079 = image_075_079 := by
  have p1 := parse_append_eq decLine075 decLine076
    decChunk075 decChunk076
    ws_075_079_0 parse_line075 parse_line076
  have p2 := parse_append_eq (decLine075 ++ decLine076) decLine077
    (decChunk075 ++ decChunk076) decChunk077
    ws_075_079_1 p1 parse_line077
  have p3 := parse_append_eq (decLine075 ++ decLine076 ++ decLine077) decLine078
    ((decChunk075 ++ decChunk076) ++ decChunk077) decChunk078
    ws_075_079_2 p2 parse_line078
  have p4 := parse_append_eq (decLine075 ++ decLine076 ++ decLine077 ++ decLine078) decLine079
    (((decChunk075 ++ decChunk076) ++ decChunk077) ++ decChunk078) decChunk079
    ws_075_079_3 p3 parse_line079
  rw [text_075_079, image_075_079]
  exact p4
theorem extract_075_079 :
    intfmtImage.extract 1200 1280 = image_075_079 := by
  have i1 := extract_append_eq 1200 1216 1232
    decChunk075 decChunk076
    (by decide) (by decide) (by decide)
    image_chunk075 image_chunk076
  have i2 := extract_append_eq 1200 1232 1248
    (decChunk075 ++ decChunk076) decChunk077
    (by decide) (by decide) (by decide)
    i1 image_chunk077
  have i3 := extract_append_eq 1200 1248 1264
    ((decChunk075 ++ decChunk076) ++ decChunk077) decChunk078
    (by decide) (by decide) (by decide)
    i2 image_chunk078
  have i4 := extract_append_eq 1200 1264 1280
    (((decChunk075 ++ decChunk076) ++ decChunk077) ++ decChunk078) decChunk079
    (by decide) (by decide) (by decide)
    i3 image_chunk079
  rw [image_075_079]
  exact i4
private theorem ws_text_075_079 : listEndsWS text_075_079.toList := by
  unfold text_075_079
  exact ws_075_079_4

@[irreducible] def text_080_084 : String := decLine080 ++ decLine081 ++ decLine082 ++ decLine083 ++ decLine084
@[irreducible] def image_080_084 : Array UInt16 := ((((decChunk080 ++ decChunk081) ++ decChunk082) ++ decChunk083) ++ decChunk084)
private theorem ws_080_084_0 : listEndsWS decLine080.toList :=
  decLine080_ws
private theorem ws_080_084_1 : listEndsWS (decLine080 ++ decLine081).toList :=
  ws_cat (decLine080) decLine081 ws_080_084_0 decLine081_ws
private theorem ws_080_084_2 : listEndsWS (decLine080 ++ decLine081 ++ decLine082).toList :=
  ws_cat (decLine080 ++ decLine081) decLine082 ws_080_084_1 decLine082_ws
private theorem ws_080_084_3 : listEndsWS (decLine080 ++ decLine081 ++ decLine082 ++ decLine083).toList :=
  ws_cat (decLine080 ++ decLine081 ++ decLine082) decLine083 ws_080_084_2 decLine083_ws
private theorem ws_080_084_4 : listEndsWS (decLine080 ++ decLine081 ++ decLine082 ++ decLine083 ++ decLine084).toList :=
  ws_cat (decLine080 ++ decLine081 ++ decLine082 ++ decLine083) decLine084 ws_080_084_3 decLine084_ws
theorem parse_080_084 : parseDecText text_080_084 = image_080_084 := by
  have p1 := parse_append_eq decLine080 decLine081
    decChunk080 decChunk081
    ws_080_084_0 parse_line080 parse_line081
  have p2 := parse_append_eq (decLine080 ++ decLine081) decLine082
    (decChunk080 ++ decChunk081) decChunk082
    ws_080_084_1 p1 parse_line082
  have p3 := parse_append_eq (decLine080 ++ decLine081 ++ decLine082) decLine083
    ((decChunk080 ++ decChunk081) ++ decChunk082) decChunk083
    ws_080_084_2 p2 parse_line083
  have p4 := parse_append_eq (decLine080 ++ decLine081 ++ decLine082 ++ decLine083) decLine084
    (((decChunk080 ++ decChunk081) ++ decChunk082) ++ decChunk083) decChunk084
    ws_080_084_3 p3 parse_line084
  rw [text_080_084, image_080_084]
  exact p4
theorem extract_080_084 :
    intfmtImage.extract 1280 1360 = image_080_084 := by
  have i1 := extract_append_eq 1280 1296 1312
    decChunk080 decChunk081
    (by decide) (by decide) (by decide)
    image_chunk080 image_chunk081
  have i2 := extract_append_eq 1280 1312 1328
    (decChunk080 ++ decChunk081) decChunk082
    (by decide) (by decide) (by decide)
    i1 image_chunk082
  have i3 := extract_append_eq 1280 1328 1344
    ((decChunk080 ++ decChunk081) ++ decChunk082) decChunk083
    (by decide) (by decide) (by decide)
    i2 image_chunk083
  have i4 := extract_append_eq 1280 1344 1360
    (((decChunk080 ++ decChunk081) ++ decChunk082) ++ decChunk083) decChunk084
    (by decide) (by decide) (by decide)
    i3 image_chunk084
  rw [image_080_084]
  exact i4
private theorem ws_text_080_084 : listEndsWS text_080_084.toList := by
  unfold text_080_084
  exact ws_080_084_4

@[irreducible] def text_085_089 : String := decLine085 ++ decLine086 ++ decLine087 ++ decLine088 ++ decLine089
@[irreducible] def image_085_089 : Array UInt16 := ((((decChunk085 ++ decChunk086) ++ decChunk087) ++ decChunk088) ++ decChunk089)
private theorem ws_085_089_0 : listEndsWS decLine085.toList :=
  decLine085_ws
private theorem ws_085_089_1 : listEndsWS (decLine085 ++ decLine086).toList :=
  ws_cat (decLine085) decLine086 ws_085_089_0 decLine086_ws
private theorem ws_085_089_2 : listEndsWS (decLine085 ++ decLine086 ++ decLine087).toList :=
  ws_cat (decLine085 ++ decLine086) decLine087 ws_085_089_1 decLine087_ws
private theorem ws_085_089_3 : listEndsWS (decLine085 ++ decLine086 ++ decLine087 ++ decLine088).toList :=
  ws_cat (decLine085 ++ decLine086 ++ decLine087) decLine088 ws_085_089_2 decLine088_ws
private theorem ws_085_089_4 : listEndsWS (decLine085 ++ decLine086 ++ decLine087 ++ decLine088 ++ decLine089).toList :=
  ws_cat (decLine085 ++ decLine086 ++ decLine087 ++ decLine088) decLine089 ws_085_089_3 decLine089_ws
theorem parse_085_089 : parseDecText text_085_089 = image_085_089 := by
  have p1 := parse_append_eq decLine085 decLine086
    decChunk085 decChunk086
    ws_085_089_0 parse_line085 parse_line086
  have p2 := parse_append_eq (decLine085 ++ decLine086) decLine087
    (decChunk085 ++ decChunk086) decChunk087
    ws_085_089_1 p1 parse_line087
  have p3 := parse_append_eq (decLine085 ++ decLine086 ++ decLine087) decLine088
    ((decChunk085 ++ decChunk086) ++ decChunk087) decChunk088
    ws_085_089_2 p2 parse_line088
  have p4 := parse_append_eq (decLine085 ++ decLine086 ++ decLine087 ++ decLine088) decLine089
    (((decChunk085 ++ decChunk086) ++ decChunk087) ++ decChunk088) decChunk089
    ws_085_089_3 p3 parse_line089
  rw [text_085_089, image_085_089]
  exact p4
theorem extract_085_089 :
    intfmtImage.extract 1360 1440 = image_085_089 := by
  have i1 := extract_append_eq 1360 1376 1392
    decChunk085 decChunk086
    (by decide) (by decide) (by decide)
    image_chunk085 image_chunk086
  have i2 := extract_append_eq 1360 1392 1408
    (decChunk085 ++ decChunk086) decChunk087
    (by decide) (by decide) (by decide)
    i1 image_chunk087
  have i3 := extract_append_eq 1360 1408 1424
    ((decChunk085 ++ decChunk086) ++ decChunk087) decChunk088
    (by decide) (by decide) (by decide)
    i2 image_chunk088
  have i4 := extract_append_eq 1360 1424 1440
    (((decChunk085 ++ decChunk086) ++ decChunk087) ++ decChunk088) decChunk089
    (by decide) (by decide) (by decide)
    i3 image_chunk089
  rw [image_085_089]
  exact i4
private theorem ws_text_085_089 : listEndsWS text_085_089.toList := by
  unfold text_085_089
  exact ws_085_089_4

@[irreducible] def text_090_094 : String := decLine090 ++ decLine091 ++ decLine092 ++ decLine093 ++ decLine094
@[irreducible] def image_090_094 : Array UInt16 := ((((decChunk090 ++ decChunk091) ++ decChunk092) ++ decChunk093) ++ decChunk094)
private theorem ws_090_094_0 : listEndsWS decLine090.toList :=
  decLine090_ws
private theorem ws_090_094_1 : listEndsWS (decLine090 ++ decLine091).toList :=
  ws_cat (decLine090) decLine091 ws_090_094_0 decLine091_ws
private theorem ws_090_094_2 : listEndsWS (decLine090 ++ decLine091 ++ decLine092).toList :=
  ws_cat (decLine090 ++ decLine091) decLine092 ws_090_094_1 decLine092_ws
private theorem ws_090_094_3 : listEndsWS (decLine090 ++ decLine091 ++ decLine092 ++ decLine093).toList :=
  ws_cat (decLine090 ++ decLine091 ++ decLine092) decLine093 ws_090_094_2 decLine093_ws
private theorem ws_090_094_4 : listEndsWS (decLine090 ++ decLine091 ++ decLine092 ++ decLine093 ++ decLine094).toList :=
  ws_cat (decLine090 ++ decLine091 ++ decLine092 ++ decLine093) decLine094 ws_090_094_3 decLine094_ws
theorem parse_090_094 : parseDecText text_090_094 = image_090_094 := by
  have p1 := parse_append_eq decLine090 decLine091
    decChunk090 decChunk091
    ws_090_094_0 parse_line090 parse_line091
  have p2 := parse_append_eq (decLine090 ++ decLine091) decLine092
    (decChunk090 ++ decChunk091) decChunk092
    ws_090_094_1 p1 parse_line092
  have p3 := parse_append_eq (decLine090 ++ decLine091 ++ decLine092) decLine093
    ((decChunk090 ++ decChunk091) ++ decChunk092) decChunk093
    ws_090_094_2 p2 parse_line093
  have p4 := parse_append_eq (decLine090 ++ decLine091 ++ decLine092 ++ decLine093) decLine094
    (((decChunk090 ++ decChunk091) ++ decChunk092) ++ decChunk093) decChunk094
    ws_090_094_3 p3 parse_line094
  rw [text_090_094, image_090_094]
  exact p4
theorem extract_090_094 :
    intfmtImage.extract 1440 1520 = image_090_094 := by
  have i1 := extract_append_eq 1440 1456 1472
    decChunk090 decChunk091
    (by decide) (by decide) (by decide)
    image_chunk090 image_chunk091
  have i2 := extract_append_eq 1440 1472 1488
    (decChunk090 ++ decChunk091) decChunk092
    (by decide) (by decide) (by decide)
    i1 image_chunk092
  have i3 := extract_append_eq 1440 1488 1504
    ((decChunk090 ++ decChunk091) ++ decChunk092) decChunk093
    (by decide) (by decide) (by decide)
    i2 image_chunk093
  have i4 := extract_append_eq 1440 1504 1520
    (((decChunk090 ++ decChunk091) ++ decChunk092) ++ decChunk093) decChunk094
    (by decide) (by decide) (by decide)
    i3 image_chunk094
  rw [image_090_094]
  exact i4
private theorem ws_text_090_094 : listEndsWS text_090_094.toList := by
  unfold text_090_094
  exact ws_090_094_4

@[irreducible] def text_095_099 : String := decLine095 ++ decLine096 ++ decLine097 ++ decLine098 ++ decLine099
@[irreducible] def image_095_099 : Array UInt16 := ((((decChunk095 ++ decChunk096) ++ decChunk097) ++ decChunk098) ++ decChunk099)
private theorem ws_095_099_0 : listEndsWS decLine095.toList :=
  decLine095_ws
private theorem ws_095_099_1 : listEndsWS (decLine095 ++ decLine096).toList :=
  ws_cat (decLine095) decLine096 ws_095_099_0 decLine096_ws
private theorem ws_095_099_2 : listEndsWS (decLine095 ++ decLine096 ++ decLine097).toList :=
  ws_cat (decLine095 ++ decLine096) decLine097 ws_095_099_1 decLine097_ws
private theorem ws_095_099_3 : listEndsWS (decLine095 ++ decLine096 ++ decLine097 ++ decLine098).toList :=
  ws_cat (decLine095 ++ decLine096 ++ decLine097) decLine098 ws_095_099_2 decLine098_ws
private theorem ws_095_099_4 : listEndsWS (decLine095 ++ decLine096 ++ decLine097 ++ decLine098 ++ decLine099).toList :=
  ws_cat (decLine095 ++ decLine096 ++ decLine097 ++ decLine098) decLine099 ws_095_099_3 decLine099_ws
theorem parse_095_099 : parseDecText text_095_099 = image_095_099 := by
  have p1 := parse_append_eq decLine095 decLine096
    decChunk095 decChunk096
    ws_095_099_0 parse_line095 parse_line096
  have p2 := parse_append_eq (decLine095 ++ decLine096) decLine097
    (decChunk095 ++ decChunk096) decChunk097
    ws_095_099_1 p1 parse_line097
  have p3 := parse_append_eq (decLine095 ++ decLine096 ++ decLine097) decLine098
    ((decChunk095 ++ decChunk096) ++ decChunk097) decChunk098
    ws_095_099_2 p2 parse_line098
  have p4 := parse_append_eq (decLine095 ++ decLine096 ++ decLine097 ++ decLine098) decLine099
    (((decChunk095 ++ decChunk096) ++ decChunk097) ++ decChunk098) decChunk099
    ws_095_099_3 p3 parse_line099
  rw [text_095_099, image_095_099]
  exact p4
theorem extract_095_099 :
    intfmtImage.extract 1520 1600 = image_095_099 := by
  have i1 := extract_append_eq 1520 1536 1552
    decChunk095 decChunk096
    (by decide) (by decide) (by decide)
    image_chunk095 image_chunk096
  have i2 := extract_append_eq 1520 1552 1568
    (decChunk095 ++ decChunk096) decChunk097
    (by decide) (by decide) (by decide)
    i1 image_chunk097
  have i3 := extract_append_eq 1520 1568 1584
    ((decChunk095 ++ decChunk096) ++ decChunk097) decChunk098
    (by decide) (by decide) (by decide)
    i2 image_chunk098
  have i4 := extract_append_eq 1520 1584 1600
    (((decChunk095 ++ decChunk096) ++ decChunk097) ++ decChunk098) decChunk099
    (by decide) (by decide) (by decide)
    i3 image_chunk099
  rw [image_095_099]
  exact i4
private theorem ws_text_095_099 : listEndsWS text_095_099.toList := by
  unfold text_095_099
  exact ws_095_099_4

@[irreducible] def joinB_pref1 : String := text_050_054 ++ text_055_059
@[irreducible] def joinB_img1 : Array UInt16 := image_050_054 ++ image_055_059
private theorem ws_joinB_pref1 : listEndsWS joinB_pref1.toList := by
  unfold joinB_pref1
  exact ws_cat text_050_054 text_055_059 ws_text_050_054 ws_text_055_059
theorem parse_joinB_pref1 :
    parseDecText joinB_pref1 = joinB_img1 := by
  have h := parse_append_eq text_050_054 text_055_059 image_050_054 image_055_059
    ws_text_050_054 parse_050_054 parse_055_059
  unfold joinB_pref1 joinB_img1
  exact h
theorem extract_joinB_pref1 :
    intfmtImage.extract 800 960 = joinB_img1 := by
  have h := extract_append_eq 800 880 960 image_050_054 image_055_059
    (by decide) (by decide) (by decide)
    extract_050_054 extract_055_059
  unfold joinB_img1
  exact h
@[irreducible] def joinB_pref2 : String := joinB_pref1 ++ text_060_064
@[irreducible] def joinB_img2 : Array UInt16 := joinB_img1 ++ image_060_064
private theorem ws_joinB_pref2 : listEndsWS joinB_pref2.toList := by
  unfold joinB_pref2
  exact ws_cat joinB_pref1 text_060_064 ws_joinB_pref1 ws_text_060_064
theorem parse_joinB_pref2 :
    parseDecText joinB_pref2 = joinB_img2 := by
  have h := parse_append_eq joinB_pref1 text_060_064
    joinB_img1 image_060_064
    ws_joinB_pref1 parse_joinB_pref1 parse_060_064
  unfold joinB_pref2 joinB_img2
  exact h
theorem extract_joinB_pref2 :
    intfmtImage.extract 800 1040 = joinB_img2 := by
  have h := extract_append_eq 800 960 1040
    joinB_img1 image_060_064
    (by decide) (by decide) (by decide)
    extract_joinB_pref1 extract_060_064
  unfold joinB_img2
  exact h
@[irreducible] def joinB_pref3 : String := joinB_pref2 ++ text_065_069
@[irreducible] def joinB_img3 : Array UInt16 := joinB_img2 ++ image_065_069
private theorem ws_joinB_pref3 : listEndsWS joinB_pref3.toList := by
  unfold joinB_pref3
  exact ws_cat joinB_pref2 text_065_069 ws_joinB_pref2 ws_text_065_069
theorem parse_joinB_pref3 :
    parseDecText joinB_pref3 = joinB_img3 := by
  have h := parse_append_eq joinB_pref2 text_065_069
    joinB_img2 image_065_069
    ws_joinB_pref2 parse_joinB_pref2 parse_065_069
  unfold joinB_pref3 joinB_img3
  exact h
theorem extract_joinB_pref3 :
    intfmtImage.extract 800 1120 = joinB_img3 := by
  have h := extract_append_eq 800 1040 1120
    joinB_img2 image_065_069
    (by decide) (by decide) (by decide)
    extract_joinB_pref2 extract_065_069
  unfold joinB_img3
  exact h
@[irreducible] def joinB_pref4 : String := joinB_pref3 ++ text_070_074
@[irreducible] def joinB_img4 : Array UInt16 := joinB_img3 ++ image_070_074
private theorem ws_joinB_pref4 : listEndsWS joinB_pref4.toList := by
  unfold joinB_pref4
  exact ws_cat joinB_pref3 text_070_074 ws_joinB_pref3 ws_text_070_074
theorem parse_joinB_pref4 :
    parseDecText joinB_pref4 = joinB_img4 := by
  have h := parse_append_eq joinB_pref3 text_070_074
    joinB_img3 image_070_074
    ws_joinB_pref3 parse_joinB_pref3 parse_070_074
  unfold joinB_pref4 joinB_img4
  exact h
theorem extract_joinB_pref4 :
    intfmtImage.extract 800 1200 = joinB_img4 := by
  have h := extract_append_eq 800 1120 1200
    joinB_img3 image_070_074
    (by decide) (by decide) (by decide)
    extract_joinB_pref3 extract_070_074
  unfold joinB_img4
  exact h
@[irreducible] def joinB_pref5 : String := joinB_pref4 ++ text_075_079
@[irreducible] def joinB_img5 : Array UInt16 := joinB_img4 ++ image_075_079
private theorem ws_joinB_pref5 : listEndsWS joinB_pref5.toList := by
  unfold joinB_pref5
  exact ws_cat joinB_pref4 text_075_079 ws_joinB_pref4 ws_text_075_079
theorem parse_joinB_pref5 :
    parseDecText joinB_pref5 = joinB_img5 := by
  have h := parse_append_eq joinB_pref4 text_075_079
    joinB_img4 image_075_079
    ws_joinB_pref4 parse_joinB_pref4 parse_075_079
  unfold joinB_pref5 joinB_img5
  exact h
theorem extract_joinB_pref5 :
    intfmtImage.extract 800 1280 = joinB_img5 := by
  have h := extract_append_eq 800 1200 1280
    joinB_img4 image_075_079
    (by decide) (by decide) (by decide)
    extract_joinB_pref4 extract_075_079
  unfold joinB_img5
  exact h
@[irreducible] def joinB_pref6 : String := joinB_pref5 ++ text_080_084
@[irreducible] def joinB_img6 : Array UInt16 := joinB_img5 ++ image_080_084
private theorem ws_joinB_pref6 : listEndsWS joinB_pref6.toList := by
  unfold joinB_pref6
  exact ws_cat joinB_pref5 text_080_084 ws_joinB_pref5 ws_text_080_084
theorem parse_joinB_pref6 :
    parseDecText joinB_pref6 = joinB_img6 := by
  have h := parse_append_eq joinB_pref5 text_080_084
    joinB_img5 image_080_084
    ws_joinB_pref5 parse_joinB_pref5 parse_080_084
  unfold joinB_pref6 joinB_img6
  exact h
theorem extract_joinB_pref6 :
    intfmtImage.extract 800 1360 = joinB_img6 := by
  have h := extract_append_eq 800 1280 1360
    joinB_img5 image_080_084
    (by decide) (by decide) (by decide)
    extract_joinB_pref5 extract_080_084
  unfold joinB_img6
  exact h
@[irreducible] def joinB_pref7 : String := joinB_pref6 ++ text_085_089
@[irreducible] def joinB_img7 : Array UInt16 := joinB_img6 ++ image_085_089
private theorem ws_joinB_pref7 : listEndsWS joinB_pref7.toList := by
  unfold joinB_pref7
  exact ws_cat joinB_pref6 text_085_089 ws_joinB_pref6 ws_text_085_089
theorem parse_joinB_pref7 :
    parseDecText joinB_pref7 = joinB_img7 := by
  have h := parse_append_eq joinB_pref6 text_085_089
    joinB_img6 image_085_089
    ws_joinB_pref6 parse_joinB_pref6 parse_085_089
  unfold joinB_pref7 joinB_img7
  exact h
theorem extract_joinB_pref7 :
    intfmtImage.extract 800 1440 = joinB_img7 := by
  have h := extract_append_eq 800 1360 1440
    joinB_img6 image_085_089
    (by decide) (by decide) (by decide)
    extract_joinB_pref6 extract_085_089
  unfold joinB_img7
  exact h
@[irreducible] def joinB_pref8 : String := joinB_pref7 ++ text_090_094
@[irreducible] def joinB_img8 : Array UInt16 := joinB_img7 ++ image_090_094
private theorem ws_joinB_pref8 : listEndsWS joinB_pref8.toList := by
  unfold joinB_pref8
  exact ws_cat joinB_pref7 text_090_094 ws_joinB_pref7 ws_text_090_094
theorem parse_joinB_pref8 :
    parseDecText joinB_pref8 = joinB_img8 := by
  have h := parse_append_eq joinB_pref7 text_090_094
    joinB_img7 image_090_094
    ws_joinB_pref7 parse_joinB_pref7 parse_090_094
  unfold joinB_pref8 joinB_img8
  exact h
theorem extract_joinB_pref8 :
    intfmtImage.extract 800 1520 = joinB_img8 := by
  have h := extract_append_eq 800 1440 1520
    joinB_img7 image_090_094
    (by decide) (by decide) (by decide)
    extract_joinB_pref7 extract_090_094
  unfold joinB_img8
  exact h
@[irreducible] def joinB_pref9 : String := joinB_pref8 ++ text_095_099
@[irreducible] def joinB_img9 : Array UInt16 := joinB_img8 ++ image_095_099
private theorem ws_joinB_pref9 : listEndsWS joinB_pref9.toList := by
  unfold joinB_pref9
  exact ws_cat joinB_pref8 text_095_099 ws_joinB_pref8 ws_text_095_099
theorem parse_joinB_pref9 :
    parseDecText joinB_pref9 = joinB_img9 := by
  have h := parse_append_eq joinB_pref8 text_095_099
    joinB_img8 image_095_099
    ws_joinB_pref8 parse_joinB_pref8 parse_095_099
  unfold joinB_pref9 joinB_img9
  exact h
theorem extract_joinB_pref9 :
    intfmtImage.extract 800 1600 = joinB_img9 := by
  have h := extract_append_eq 800 1520 1600
    joinB_img8 image_095_099
    (by decide) (by decide) (by decide)
    extract_joinB_pref8 extract_095_099
  unfold joinB_img9
  exact h
@[irreducible] def joinBText : String := joinB_pref9
@[irreducible] def joinBImage : Array UInt16 := joinB_img9
theorem parse_joinB : parseDecText joinBText = joinBImage := by
  unfold joinBText joinBImage
  exact parse_joinB_pref9
theorem extract_joinB :
    intfmtImage.extract 800 1600 = joinBImage := by
  unfold joinBImage
  exact extract_joinB_pref9
theorem ws_joinB : listEndsWS joinBText.toList := by
  unfold joinBText
  exact ws_joinB_pref9

end IntFmt

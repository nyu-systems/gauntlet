--- dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:32:29.913111600 +0200
+++ dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:32:29.916050100 +0200
@@ -40,6 +40,11 @@ control update(inout packet_t h, inout M
     }
 }
 control ingress(inout packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
+    bit<8> reg;
+    bit<8> reg_1;
+    bit<8> reg_2;
+    bit<8> reg_3;
+    bit<16> key_0;
     @name("ingress.setb1") action setb1_0(bit<9> port, bit<8> val) {
         hdrs.data.b1 = val;
         meta.egress_spec = port;
@@ -54,22 +59,18 @@ control ingress(inout packet_t hdrs, ino
     }
     @name("ingress.noop") action noop_8() {
     }
-    bit<8> reg;
     @name("ingress.setbyte") action setbyte_0(bit<8> val) {
         reg = val;
         hdrs.extra[0].b1 = reg;
     }
-    bit<8> reg_1;
     @name("ingress.setbyte") action setbyte_4(bit<8> val) {
         reg_1 = val;
         hdrs.data.b2 = reg_1;
     }
-    bit<8> reg_2;
     @name("ingress.setbyte") action setbyte_5(bit<8> val) {
         reg_2 = val;
         hdrs.extra[1].b1 = reg_2;
     }
-    bit<8> reg_3;
     @name("ingress.setbyte") action setbyte_6(bit<8> val) {
         reg_3 = val;
         hdrs.extra[2].b2 = reg_3;
@@ -93,7 +94,6 @@ control ingress(inout packet_t hdrs, ino
         }
         default_action = noop_0();
     }
-    bit<16> key_0;
     @name("ingress.ex1") table ex1 {
         key = {
             key_0: ternary @name("hdrs.extra[0].h") ;

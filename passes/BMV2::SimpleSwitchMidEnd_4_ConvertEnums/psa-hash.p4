--- dumps/pruned/psa-hash-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:20.441229300 +0200
+++ dumps/pruned/psa-hash-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-06-08 18:33:20.445063300 +0200
@@ -26,7 +26,7 @@ control MyIC(inout ethernet_t a, inout u
     bit<16> tmp_0;
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.h") Hash<bit<16>>(PSA_HashAlgorithm_t.CRC16) h;
+    @name("MyIC.h") Hash<bit<16>>(32w3) h;
     @name("MyIC.a1") action a1_0() {
         tmp_0 = h.get_hash<ethernet_t>(a);
         b.data = tmp_0;

--- dumps/p4_16_samples/psa-hash.p4/pruned/psa-hash-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:47.515420300 +0200
+++ dumps/p4_16_samples/psa-hash.p4/pruned/psa-hash-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:31:47.519303800 +0200
@@ -26,7 +26,7 @@ control MyIC(inout ethernet_t a, inout u
     bit<16> tmp_0;
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.h") Hash<bit<16>>(PSA_HashAlgorithm_t.CRC16) h;
+    @name("MyIC.h") Hash<bit<16>>(32w3) h;
     @name("MyIC.a1") action a1_0() {
         tmp_0 = h.get_hash<ethernet_t>(a);
         b.data = tmp_0;

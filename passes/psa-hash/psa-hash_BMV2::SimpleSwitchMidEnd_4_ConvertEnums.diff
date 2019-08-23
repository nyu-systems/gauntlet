--- before_pass
+++ after_pass
@@ -26,7 +26,7 @@ control MyIC(inout ethernet_t a, inout u
     bit<16> tmp;
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.h") Hash<bit<16>>(PSA_HashAlgorithm_t.CRC16) h_0;
+    @name("MyIC.h") Hash<bit<16>>(32w3) h_0;
     @name("MyIC.a1") action a1() {
         tmp = h_0.get_hash<ethernet_t>(a);
         b.data = tmp;

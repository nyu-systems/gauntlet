--- dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 17:31:58.656588100 +0200
+++ dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_9_ConstantFolding.p4	2019-05-20 17:31:58.658626200 +0200
@@ -28,7 +28,7 @@ control c(inout Headers h) {
             if (h.eth.type == 16w0x800) 
                 h.eth.setInvalid();
             else 
-                h.eth.type = (bit<16>)16w0;
+                h.eth.type = 16w0;
     }
 }
 parser p<H>(packet_in _p, out H h);

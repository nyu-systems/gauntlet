--- dumps/p4_16_samples/bfd_offload.p4/pruned/bfd_offload-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:12.034890600 +0200
+++ dumps/p4_16_samples/bfd_offload.p4/pruned/bfd_offload-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:12.037096500 +0200
@@ -11,15 +11,11 @@ BFD_Offload(16w32768) bfd_session_livene
     }
     bool on_tx(in bit<16> index) {
         bit<8> tmp_1;
-        bit<8> tmp_2;
-        bit<8> c;
         tmp_1 = this.getTx(index);
-        tmp_2 = tmp_1 + 8w1;
-        c = tmp_2;
-        if (c >= 8w4) 
+        if (tmp_1 + 8w1 >= 8w4) 
             return true;
         else {
-            this.setTx(index, c);
+            this.setTx(index, tmp_1 + 8w1);
             return false;
         }
     }

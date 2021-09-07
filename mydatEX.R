
rm(list = ls())

# install.packages("randomForestSRC")

install.packages("pec")
install.packages("sampling")
install.packages("survivalROC")
install.packages("survAUC")
install.packages("pROC")
install.packages("PRROC")
install.packages("randomForestSRC")

#### 导入包和自定义函数 ####
library("mfp")
library("survMisc")
library("Hmisc")
library("compareC")
library("rms")
library(sampling)
library(survivalROC)
library(survAUC)
library(pROC)
library(PRROC)
library(randomForestSRC)

{
  c.f.text <- function(c.f){
    c.f.cindex <- max(c.f[1], 1-c.f[1])
    c.f.SE.196 <- 1.96*c.f[3]/2
    c.f.value <- round(c(c.f.cindex,max(c.f.cindex-c.f.SE.196,0),min(c.f.cindex+c.f.SE.196,1)),2)
    c.f.tex <- paste0(c.f.value[1], "(", c.f.value[2], "-", c.f.value[3], ")")
    return(c.f.tex)
  }
  
  biggerzero <- function(x){
    y <- (sum(x,na.rm = T)>0)*1
    return(y)
  }
  notzerouniquenum <- function(x){
    y <- x[x!=0]
    return(length(unique(y)))
  }
  survivalROC.me <- function (Stime, status, marker, entry = NULL, predict.time, 
                              cut.values = NULL, method = "NNE", lambda = NULL, span = NULL, 
                              window = "symmetric"){
    times = Stime
    x <- marker
    if (is.null(entry)) 
      entry <- rep(0, length(times))
    bad <- is.na(times) | is.na(status) | is.na(x) | is.na(entry)
    entry <- entry[!bad]
    times <- times[!bad]
    status <- status[!bad]
    x <- x[!bad]
    if (sum(bad) > 0) 
      cat(paste("\n", sum(bad), "records with missing values dropped. \n"))
    if (is.null(cut.values)) 
      cut.values <- unique(x)
    cut.values <- cut.values[order(cut.values)]
    ncuts <- length(cut.values)
    ooo <- order(times)
    times <- times[ooo]
    status <- status[ooo]
    x <- x[ooo]
    s0 <- 1
    unique.t0 <- unique(times)
    unique.t0 <- unique.t0[order(unique.t0)]
    n.times <- sum(unique.t0 <= predict.time)
    for (j in 1:n.times) {
      n <- sum(entry <= unique.t0[j] & times >= unique.t0[j])
      d <- sum((entry <= unique.t0[j]) & (times == unique.t0[j]) & 
                 (status == 1))
      if (n > 0) 
        s0 <- s0 * (1 - d/n)
    }
    s.pooled <- s0
    roc.matrix <- matrix(NA, ncuts, 2)
    roc.matrix[ncuts, 1] <- 0
    roc.matrix[ncuts, 2] <- 1
    if (method == "KM") {
      for (c in 1:(ncuts - 1)) {
        s0 <- 1
        subset <- as.logical(x > cut.values[c])
        e0 <- entry[subset]
        t0 <- times[subset]
        c0 <- status[subset]
        if (!is.null(t0)) {
          unique.t0 <- unique(t0)
          unique.t0 <- unique.t0[order(unique.t0)]
          n.times <- sum(unique.t0 <= predict.time)
          if (n.times > 0) {
            for (j in 1:n.times) {
              n <- sum(e0 <= unique.t0[j] & t0 >= unique.t0[j])
              d <- sum((e0 <= unique.t0[j]) & (t0 == unique.t0[j]) & 
                         (c0 == 1))
              if (n > 0) 
                s0 <- s0 * (1 - d/n)
            }
          }
        }
        p0 <- mean(subset)
        roc.matrix[c, 1] <- (1 - s0) * p0/(1 - s.pooled)
        roc.matrix[c, 2] <- 1 - s0 * p0/s.pooled
      }
    }
    if (method == "NNE") {
      if (is.null(lambda) & is.null(span)) {
        cat("method = NNE requires either lambda or span! \n")
        stop(0)
      }
      x.unique <- unique(x)
      x.unique <- x.unique[order(x.unique)]
      S.t.x <- rep(0, length(x.unique))
      t.evaluate <- unique(times[status == 1])
      t.evaluate <- t.evaluate[order(t.evaluate)]
      t.evaluate <- t.evaluate[t.evaluate <= predict.time]
      for (j in 1:length(x.unique)) {
        if (!is.null(span)) {
          if (window == "symmetric") {
            ddd <- (x - x.unique[j])
            n <- length(x)
            ddd <- ddd[order(ddd)]
            index0 <- sum(ddd < 0) + 1
            index1 <- index0 + trunc(n * span + 0.5)
            if (index1 > n) 
              index1 <- n
            lambda <- ddd[index1]
            wt <- as.integer(((x - x.unique[j]) <= lambda) & 
                               ((x - x.unique[j]) >= 0))
            index0 <- sum(ddd <= 0)
            index2 <- index0 - trunc(n * span/2)
            if (index2 < 1) 
              index2 <- 1
            lambda <- abs(ddd[index1])
            set.index <- ((x - x.unique[j]) >= -lambda) & 
              ((x - x.unique[j]) <= 0)
            wt[set.index] <- 1
          }
          if (window == "asymmetric") {
            ddd <- (x - x.unique[j])
            n <- length(x)
            ddd <- ddd[order(ddd)]
            index0 <- sum(ddd < 0) + 1
            index <- index0 + trunc(n * span)
            if (index > n) 
              index <- n
            lambda <- ddd[index]
            wt <- as.integer(((x - x.unique[j]) <= lambda) & 
                               ((x - x.unique[j]) >= 0))
          }
        }
        else {
          wt <- exp(-(x - x.unique[j])^2/lambda^2)
        }
        s0 <- 1
        for (k in 1:length(t.evaluate)) {
          n <- sum(wt * (entry <= t.evaluate[k]) & (times >= 
                                                      t.evaluate[k]))
          d <- sum(wt * (entry <= t.evaluate[k]) & (times == 
                                                      t.evaluate[k]) * (status == 1))
          if (n > 0) 
            s0 <- s0 * (1 - d/n)
        }
        S.t.x[j] <- s0
      }
      S.all.x <- S.t.x[match(x, x.unique)]
      n <- length(times)
      S.marginal <- sum(S.all.x)/n
      for (c in 1:(ncuts - 1)) {
        p1 <- sum(x > cut.values[c])/n
        Sx <- sum(S.all.x[x > cut.values[c]])/n
        roc.matrix[c, 1] <- (p1 - Sx)/(1 - S.marginal)
        roc.matrix[c, 2] <- 1 - Sx/S.marginal
      }
    }
    sensitivity = roc.matrix[, 1]
    specificity = roc.matrix[, 2]
    x <- 1 - c(0, specificity)
    y <- c(1, sensitivity)
    n <- length(x)
    dx <- x[-n] - x[-1]
    mid.y <- (y[-n] + y[-1])/2
    area <- sum(dx * mid.y)
    list(cut.values = c(-Inf, cut.values), TP = y, FP = x, predict.time = predict.time, 
         Survival = s.pooled, AUC = area,sensitivity=sensitivity,specificity=specificity,roc.matrix=roc.matrix)
  }
  
  c.f.text <- function(c.f){
    c.f.cindex <- max(c.f[1], 1-c.f[1])
    c.f.SE.196 <- 1.96*c.f[3]/2
    c.f.value <- round(c(c.f.cindex,max(c.f.cindex-c.f.SE.196,0),min(c.f.cindex+c.f.SE.196,1)),3)
    c.f.tex <- paste0(c.f.value[1], "(", c.f.value[2], "-", c.f.value[3], ")")
    return(c.f.tex)
  }
  c.f.text <- function(c.f){
    c.f.cindex <- max(c.f[1], 1-c.f[1])
    c.f.SE.196 <- 1.96*c.f[3]/2
    c.f.value <- round(c(c.f.cindex,max(c.f.cindex-c.f.SE.196,0),min(c.f.cindex+c.f.SE.196,1)),2)
    c.f.tex <- paste0(c.f.value[1], "(", c.f.value[2], "-", c.f.value[3], ")")
    return(c.f.tex)
  }
  my.sens.spec <- function(a,b,c,y,lp,cutoff){
    x <- a
    a <- a[x>cutoff]
    b <- b[x>cutoff]
    c <- c[x>cutoff]
    yue <- a+b
    my.max.id <- which(yue == max(yue))
    my.conf.matr <- table(y, lp>c[my.max.id])
    e1 <- my.conf.matr[2,2]
    n1 <- sum(my.conf.matr[2,])
    p1 <- e1 / n1
    sp1 <- sqrt(p1*(1-p1)/n1)
    text1 <- paste0("sens=",round(p1,3),"(",round(p1-1.96*sp1,3),"-",round(p1+1.96*sp1,3),")")
    e2 <- my.conf.matr[1,1]
    n2 <- sum(my.conf.matr[1,])
    p2 <- e2 / n2
    sp2 <- sqrt(p2*(1-p2)/n2)
    text2 <- paste0("spec=",round(p2,3),"(",round(p2-1.96*sp2,3),"-",round(p2+1.96*sp2,3),")")
    text3 <- paste0("thresholds=",c[my.max.id])
    outcome <- list()
    outcome$text <- c(text1, text2,text3)
    outcome$sens <- paste0(round(p1,3),"(",round(p1-1.96*sp1,3),"-",round(p1+1.96*sp1,3),")")
    outcome$spec <- paste0(round(p2,3),"(",round(p2-1.96*sp2,3),"-",round(p2+1.96*sp2,3),")")
    outcome$thershold <- c[my.max.id]
    outcome$conf.mat <- my.conf.matr
    return(outcome)
  }
}


#### 读取数据，处理 ####
# 设置工作目录
# setwd("C:\\Users\\35578\\Desktop\\肿瘤cox")
setwd("C:\\Users\\35578\\Desktop\\肿瘤cox\\新数据")

# 读入数据
mydat0 <- read.csv("1640RDD_Version2.csv")
valdat1 <-read.csv("1val_DG.csv")
valdat2 <-read.csv("1val_FS.csv")

valdat1.x <- valdat1[,1:39]
names(valdat1.x) <- names(valdat2)
mydat.out <- rbind(valdat1.x, valdat2)

# 生成新变量
# names(mydat)
mydat0$TvLv <- mydat0$Tv + mydat0$Lv
y1.time <- mydat0$OS
y1.status <- mydat0$OS_status
testvar.all <- c("treat","Tv","Lv","TvLv","EBVDNA","T","N","stage","age","EA","VCA")
mydat0$T <- factor(as.character(mydat0$T),levels= c("1","2","3","4"), labels = c("1","2","3","4"))
mydat0$N <- factor(as.character(mydat0$N),levels= c("0","1","2","3"), labels = c("0","1","2","3"))
mydat0$stage <- factor(as.character(mydat0$stage),levels= c("2","3","4"), labels = c("2","3","4"))
mydat0$treat <- factor(as.character(mydat0$treat),levels= c("1","2"), labels = c("1","2"))
mydat.out$stage <- factor(as.character(mydat.out$stage),levels= c("2","3","4"), labels = c("2","3","4"))
mydat.out$treat <- factor(as.character(mydat.out$treat),levels= c("1","2"), labels = c("1","2"))

#### 开始大循环 ####
my.seed.time <- 999
my.outcome.length <- my.seed.time+1
my.seed.start <- 200001 # 222222
my.seed.vec <- my.seed.start:(my.seed.start+my.seed.time)
my.cindex.OS.mydat <- my.cindex.OS.mydat.val <- my.cindex.OS.mydat.out <- 
  my.cindex.PFS.mydat <- my.cindex.PFS.mydat.val <- my.cindex.PFS.mydat.out <- 
  RFSRC.cindex.OS.mydat <- RFSRC.cindex.OS.mydat.val <- RFSRC.cindex.OS.mydat.out <- 
  RFSRC.cindex.PFS.mydat <- RFSRC.cindex.PFS.mydat.val <- RFSRC.cindex.PFS.mydat.out <- 
  p.treat.OS <- p.treat.PFS <-  character(my.outcome.length)
for (my.rand.seed.i in 1:my.outcome.length) {
  
  # 抽样
  set.seed(my.seed.vec[my.rand.seed.i])
  sub_train <- strata(mydat0, stratanames = "OS_status", size = c(1075,74), method = "srswor")
  mydat <- mydat0[sub_train$ID_unit,]
  mydat.val <- mydat0[-sub_train$ID_unit,]
  
  # 计算不同变量的fp值
  # Tv
  temp.f <- mfp(Surv(OS, OS_status) ~ Tv, family = cox, data = mydat)
  temp.trafo <- temp.f$trafo
  temp.com.Tv.mydat <- paste0("mydat$Tv.fp <- ",temp.trafo[1,])
  temp.com.Tv.mydat.val <- paste0("mydat.val$Tv.fp <- ",temp.trafo[1,])
  temp.com.Tv.mydat.out <- paste0("mydat.out$Tv.fp <- ",temp.trafo[1,])
  # Lv
  temp.f <- mfp(Surv(OS, OS_status) ~ Lv, family = cox, data = mydat)
  temp.trafo <- temp.f$trafo
  temp.com.Lv.mydat <- paste0("mydat$Lv.fp <- ",temp.trafo[1,])
  temp.com.Lv.mydat.val <- paste0("mydat.val$Lv.fp <- ",temp.trafo[1,])
  temp.com.Lv.mydat.out <- paste0("mydat.out$Lv.fp <- ",temp.trafo[1,])
  # EBVDNA
  temp.f <- mfp(Surv(OS, OS_status) ~ EBVDNA, family = cox, data = mydat)
  temp.trafo <- temp.f$trafo
  temp.com.EBVDNA.mydat <- paste0("mydat$EBVDNA.fp <- ",temp.trafo[1,])
  temp.com.EBVDNA.mydat.val <- paste0("mydat.val$EBVDNA.fp <- ",temp.trafo[1,])
  temp.com.EBVDNA.mydat.out <- paste0("mydat.out$EBVDNA.fp <- ",temp.trafo[1,])
  # treat
  temp.f <- coxph(Surv(OS, OS_status) ~ treat, data = mydat)
  p.treat.OS[my.rand.seed.i] <- round(summary(temp.f)$coefficients[,5],3)
  temp.f <- coxph(Surv(PFS, PFS_status) ~ treat, data = mydat)
  p.treat.PFS[my.rand.seed.i] <- round(summary(temp.f)$coefficients[,5],3)
  
  attach(mydat,warn.conflicts = F)
  eval(parse(text = temp.com.Tv.mydat))
  eval(parse(text = temp.com.Lv.mydat))
  eval(parse(text = temp.com.EBVDNA.mydat))
  detach(mydat)
  attach(mydat.val,warn.conflicts = F)
  eval(parse(text = temp.com.Tv.mydat.val))
  eval(parse(text = temp.com.Lv.mydat.val))
  eval(parse(text = temp.com.EBVDNA.mydat.val))
  detach(mydat.val)
  attach(mydat.out,warn.conflicts = F)
  eval(parse(text = temp.com.Tv.mydat.out))
  eval(parse(text = temp.com.Lv.mydat.out))
  eval(parse(text = temp.com.EBVDNA.mydat.out))
  detach(mydat.out)
  
  #### 计算模型 并 比较 ####
  # 训练集-OS结局
  f.model.4.OS.mydat <- coxph(Surv(OS, OS_status) ~ EBVDNA.fp + stage + treat + Tv.fp + Lv.fp, data = mydat)
  c.f.4.OS.mydat <- rcorr.cens(predict(f.model.4.OS.mydat), Surv(mydat$OS, mydat$OS_status))
  my.cindex.OS.mydat[my.rand.seed.i] <- c.f.text(c.f.4.OS.mydat)
  # 测试集-OS结局
  # f.model.4.OS.mydat.val <- coxph(Surv(OS, OS_status) ~ EBVDNA.fp + stage + treat + Tv.fp + Lv.fp, data = mydat.val)
  c.f.4.OS.mydat.val <- rcorr.cens(predict(f.model.4.OS.mydat, newdata = mydat.val), Surv(mydat.val$OS, mydat.val$OS_status))
  my.cindex.OS.mydat.val[my.rand.seed.i] <- c.f.text(c.f.4.OS.mydat.val)
  # 外部验证集-OS结局
  # f.model.4.OS.mydat.out <- coxph(Surv(OS, OS_status) ~ EBVDNA.fp + stage + treat + Tv.fp + Lv.fp, data = mydat.out)
  c.f.4.OS.mydat.out <- rcorr.cens(predict(f.model.4.OS.mydat, newdata = mydat.out), Surv(mydat.out$OS, mydat.out$OS_status))
  my.cindex.OS.mydat.out[my.rand.seed.i] <- c.f.text(c.f.4.OS.mydat.out)
  
  # 训练集-PFS结局
  f.model.4.PFS.mydat <- coxph(Surv(PFS, PFS_status) ~ EBVDNA.fp + stage + treat + Tv.fp + Lv.fp, data = mydat)
  c.f.4.PFS.mydat <- rcorr.cens(predict(f.model.4.PFS.mydat), Surv(mydat$PFS, mydat$PFS_status))
  my.cindex.PFS.mydat[my.rand.seed.i] <- c.f.text(c.f.4.PFS.mydat)
  # 测试集-PFS结局
  # f.model.4.PFS.mydat.val <- coxph(Surv(PFS, PFS_status) ~ EBVDNA.fp + stage + treat + Tv.fp + Lv.fp, data = mydat.val)
  c.f.4.PFS.mydat.val <- rcorr.cens(predict(f.model.4.PFS.mydat, newdata = mydat.val), Surv(mydat.val$PFS, mydat.val$PFS_status))
  my.cindex.PFS.mydat.val[my.rand.seed.i] <- c.f.text(c.f.4.PFS.mydat.val)
  # 外部验证集-PFS结局
  # f.model.4.PFS.mydat.out <- coxph(Surv(PFS, PFS_status) ~ EBVDNA.fp + stage + treat + Tv.fp + Lv.fp, data = mydat.out)
  c.f.4.PFS.mydat.out <- rcorr.cens(predict(f.model.4.PFS.mydat, newdata = mydat.out), Surv(mydat.out$PFS, mydat.out$PFS_status))
  my.cindex.PFS.mydat.out[my.rand.seed.i] <- c.f.text(c.f.4.PFS.mydat.out)
  
  # Survival Forest for OS
  modRFSRC.OS <- rfsrc(Surv(OS, OS_status) ~ EBVDNA + stage + treat + Tv + Lv, data = mydat, ntree=500)
  RFSRC.OS.mydat <- rcorr.cens(predict(modRFSRC.OS)$predicted, Surv(mydat$OS, mydat$OS_status))
  RFSRC.cindex.OS.mydat[my.rand.seed.i] <- c.f.text(RFSRC.OS.mydat)
  RFSRC.OS.mydat.val <- rcorr.cens(predict(modRFSRC.OS, newdata = mydat.val)$predicted, Surv(mydat.val$OS, mydat.val$OS_status))
  RFSRC.cindex.OS.mydat.val[my.rand.seed.i] <- c.f.text(RFSRC.OS.mydat.val)
  RFSRC.OS.mydat.out <- rcorr.cens(predict(modRFSRC.OS, newdata = mydat.out)$predicted, Surv(mydat.out$OS, mydat.out$OS_status))
  RFSRC.cindex.OS.mydat.out[my.rand.seed.i] <- c.f.text(RFSRC.OS.mydat.out)
  
  # Survival Forest for PFS
  modRFSRC.PFS <- rfsrc(Surv(PFS, PFS_status) ~ EBVDNA + stage + treat + Tv + Lv, data = mydat, ntree=500)
  RFSRC.PFS.mydat <- rcorr.cens(predict(modRFSRC.PFS)$predicted, Surv(mydat$PFS, mydat$PFS_status))
  RFSRC.cindex.PFS.mydat[my.rand.seed.i] <- c.f.text(RFSRC.PFS.mydat)
  RFSRC.PFS.mydat.val <- rcorr.cens(predict(modRFSRC.PFS, newdata = mydat.val)$predicted, Surv(mydat.val$PFS, mydat.val$PFS_status))
  RFSRC.cindex.PFS.mydat.val[my.rand.seed.i] <- c.f.text(RFSRC.PFS.mydat.val)
  RFSRC.PFS.mydat.out <- rcorr.cens(predict(modRFSRC.PFS, newdata = mydat.out)$predicted, Surv(mydat.out$PFS, mydat.out$PFS_status))
  RFSRC.cindex.PFS.mydat.out[my.rand.seed.i] <- c.f.text(RFSRC.PFS.mydat.out)
  
  if (my.rand.seed.i %% 50 == 0) {
    print(paste0(my.rand.seed.i,"/",my.outcome.length))
  }

  
}

my.loop.outcome <- data.frame(seed=my.seed.vec,
                              Cox.cindex.OS.training=my.cindex.OS.mydat,
                              Cox.cindex.OS.test=my.cindex.OS.mydat.val,
                              Cox.cindex.OS.out=my.cindex.OS.mydat.out,
                              Cox.cindex.PFS.training=my.cindex.PFS.mydat,
                              Cox.cindex.PFS.test=my.cindex.PFS.mydat.val,
                              Cox.cindex.PFS.out=my.cindex.PFS.mydat.out,
                              p.treat.PFS = p.treat.PFS,
                              p.treat.OS = p.treat.OS,
                              RFSRC.cindex.OS.training=RFSRC.cindex.OS.mydat,
                              RFSRC.cindex.OS.test=RFSRC.cindex.OS.mydat.val,
                              RFSRC.cindex.OS.out=RFSRC.cindex.OS.mydat.out,
                              RFSRC.cindex.PFS.training=RFSRC.cindex.PFS.mydat,
                              RFSRC.cindex.PFS.test=RFSRC.cindex.PFS.mydat.val,
                              RFSRC.cindex.PFS.out=RFSRC.cindex.PFS.mydat.out)

write.csv(my.loop.outcome,"不同种子数结果20210614.csv")





####################  my round 2  ############################################

{library(pec)
library("mfp")
library("survMisc")
library("Hmisc")
library("compareC")
library("rms")
library(sampling)
library(survivalROC)
library(survAUC)
library(pROC)
library(PRROC)
library(randomForestSRC)}
c.f.text <- function(c.f){
  c.f.cindex <- max(c.f[1], 1-c.f[1])
  c.f.SE.196 <- 1.96*c.f[3]/2
  c.f.value <- round(c(c.f.cindex,max(c.f.cindex-c.f.SE.196,0),min(c.f.cindex+c.f.SE.196,1)),2)
  c.f.tex <- paste0(c.f.value[1], "(", c.f.value[2], "-", c.f.value[3], ")")
  return(c.f.tex)
}


setwd("C:\\Users\\35578\\Desktop\\肿瘤cox\\新数据")

# 读入数据
mydat0 <- read.csv("1640RDD_Version2.csv")
valdat1 <-read.csv("1val_DG.csv")
valdat2 <-read.csv("1val_FS.csv")

valdat1.x <- valdat1[,1:39]
names(valdat1.x) <- names(valdat2)
mydat.out <- rbind(valdat1.x, valdat2)

mydat0$TvLv <- mydat0$Tv + mydat0$Lv
y1.time <- mydat0$OS
y1.status <- mydat0$OS_status
testvar.all <- c("treat","Tv","Lv","TvLv","EBVDNA","T","N","stage","age","EA","VCA")
mydat0$T <- factor(as.character(mydat0$T),levels= c("1","2","3","4"), labels = c("1","2","3","4"))
mydat0$N <- factor(as.character(mydat0$N),levels= c("0","1","2","3"), labels = c("0","1","2","3"))
mydat0$stage <- factor(as.character(mydat0$stage),levels= c("2","3","4"), labels = c("2","3","4"))
mydat0$treat <- factor(as.character(mydat0$treat),levels= c("1","2"), labels = c("1","2"))
mydat.out$stage <- factor(as.character(mydat.out$stage),levels= c("2","3","4"), labels = c("2","3","4"))
mydat.out$treat <- factor(as.character(mydat.out$treat),levels= c("1","2"), labels = c("1","2"))

# seed 200562

#### xxx开始大循环xxx ####
my.seed.time <- 199
my.outcome.length <- my.seed.time+1
# my.seed.start <- 200001 # 222222
# my.seed.vec <- my.seed.start:(my.seed.start+my.seed.time)
set.seed(20210624)
my.seed.vec <- runif(my.outcome.length,1000000,2000000)

opt.ntree <- opt.nodesize <- 
  OS.cindex.test <- OS.cindex.out  <- 
  PFS.cindex.val <- PFS.cindex.test <- PFS.cindex.out <- character(my.outcome.length)

for (my.rand.seed.i in 1:my.outcome.length) {
  
  
  # 抽样生成数据
  set.seed(my.seed.vec[my.rand.seed.i])
  sub_train <- strata(mydat0, stratanames = "OS_status", size = c(1075,74), method = "srswor")
  mydat <- mydat0[sub_train$ID_unit,]  # 70%
  mydat.val.0 <- mydat0[-sub_train$ID_unit,]
  table(mydat.val.0$OS_status)
  sub_train.x <- strata(mydat.val.0, stratanames = "OS_status", size = c(306,20), method = "srswor")
  mydat.val <- mydat.val.0[-sub_train.x$ID_unit,] # 10%
  mydat.test <- mydat.val.0[sub_train.x$ID_unit,]   # 20%
  
  # 定义超参数
  m.ntree <- seq(300,800,100) # 树数
  m.nodesize <- seq(10,30,5)   # 最小节点数
  m.t <- expand.grid(m.ntree,m.nodesize)
  my.j.len <- nrow(m.t)
  # 遍历超参数列表，寻找最优参数（validation中cindex最大者）
  temp.j.cindex <- numeric(my.j.len)
  temp.j.ctext <- character(my.j.len)
  for (j in 1:nrow(m.t)) {
    
    print(paste0("[",j,"/",my.j.len,"(para)]","[",my.rand.seed.i,"/",my.outcome.length,"(peo)]","[",Sys.time(),"]"))
    
    # 1.model
    # Survival Forest for OS(Not need here)
    # modRFSRC.OS <- rfsrc(Surv(OS, OS_status) ~ EBVDNA + stage + treat + Tv + Lv + gender + age, data = mydat, ntree=m.t[j,1], nodesize=m.t[j,2])
    # Survival Forest for PFS
    modRFSRC.PFS <- rfsrc(Surv(PFS, PFS_status) ~ EBVDNA + stage + treat + Tv + Lv + gender + age, data = mydat, ntree=m.t[j,1], nodesize=m.t[j,2])
    # 2.calculate PFS validation c-index
    RFSRC.PFS.mydat.val <- rcorr.cens(predict(modRFSRC.PFS, newdata = mydat.val)$predicted, Surv(mydat.val$PFS, mydat.val$PFS_status))
    temp.j.cindex[j] <- max(RFSRC.PFS.mydat.val[1],(1-RFSRC.PFS.mydat.val[1]))
    temp.j.ctext[j] <- c.f.text(RFSRC.PFS.mydat.val)
  }
  opt.j <- which(temp.j.cindex==max(temp.j.cindex))[1]
  
  # 记录超参数
  opt.ntree[my.rand.seed.i] <- m.t[opt.j,1]
  opt.nodesize[my.rand.seed.i] <- m.t[opt.j,2]
  PFS.cindex.val[my.rand.seed.i] <- temp.j.ctext[opt.j]
  # not need now
  # valid.mat <- matrix(data=NA, nrow = length(m.ntree), ncol = length(m.nodesize))
  # for (j in 1:nrow(m.t)) {
  #   j.id.list <- expand.grid(seq_len(length(m.ntree)),seq_len(length(m.nodesize)))
  #   valid.mat[j.id.list[j,1], j.id.list[j,2]] <- temp.j.cindex[j]
  # }
  # rownames(valid.mat) <- m.ntree
  # colnames(valid.mat) <- m.nodesize
  
  # 使用超参数重新训练模型
  mydat.x2 <- rbind(mydat, mydat.val)
  # Survival Forest for OS
  modRFSRC.OS <- rfsrc(Surv(OS, OS_status) ~ EBVDNA + stage + treat + Tv + Lv + gender + age, data = mydat.x2, ntree=m.t[opt.j,1], nodesize=m.t[opt.j,2])
  # Survival Forest for PFS
  modRFSRC.PFS <- rfsrc(Surv(PFS, PFS_status) ~ EBVDNA + stage + treat + Tv + Lv + gender + age, data = mydat.x2, ntree=m.t[opt.j,1], nodesize=m.t[opt.j,2])
  
  # test set outcome
  RFSRC.PFS.mydat.test <- rcorr.cens(predict(modRFSRC.PFS, newdata = mydat.test)$predicted, Surv(mydat.test$PFS, mydat.test$PFS_status))
  PFS.cindex.test[my.rand.seed.i] <- c.f.text(RFSRC.PFS.mydat.test)
  RFSRC.OS.mydat.test <- rcorr.cens(predict(modRFSRC.OS, newdata = mydat.test)$predicted, Surv(mydat.test$OS, mydat.test$OS_status))
  OS.cindex.test[my.rand.seed.i] <- c.f.text(RFSRC.OS.mydat.test)
  
  # out outcome
  RFSRC.PFS.mydat.out <- rcorr.cens(predict(modRFSRC.PFS, newdata = mydat.out)$predicted, Surv(mydat.out$PFS, mydat.out$PFS_status))
  PFS.cindex.out[my.rand.seed.i] <- c.f.text(RFSRC.PFS.mydat.out)
  RFSRC.OS.mydat.out <- rcorr.cens(predict(modRFSRC.OS, newdata = mydat.out)$predicted, Surv(mydat.out$OS, mydat.out$OS_status))
  OS.cindex.out[my.rand.seed.i] <- c.f.text(RFSRC.OS.mydat.out)
}

my.loop.outcome <- data.frame(seed=my.seed.vec,
                              opt.ntree=opt.ntree,
                              nodesize=opt.nodesize,
                              PFS.cindex.val=PFS.cindex.val,
                              PFS.cindex.test=PFS.cindex.test,
                              PFS.cindex.out=PFS.cindex.out,
                              OS.cindex.test=OS.cindex.test,
                              OS.cindex.out=OS.cindex.out)

my.loop.outcome.x <- my.loop.outcome[1:150,]
write.csv(my.loop.outcome.x,"不同种子数结果20210624.csv")








# Survival Forest for OS
modRFSRC.OS <- rfsrc(Surv(OS, OS_status) ~ EBVDNA + stage + treat + Tv + Lv, data = mydat, ntree=500)
RFSRC.OS.mydat <- rcorr.cens(predict(modRFSRC.OS)$predicted, Surv(mydat$OS, mydat$OS_status))
c.f.text(RFSRC.OS.mydat)
RFSRC.OS.mydat.val <- rcorr.cens(predict(modRFSRC.OS, newdata = mydat.val)$predicted, Surv(mydat.val$OS, mydat.val$OS_status))
c.f.text(RFSRC.OS.mydat.val)
RFSRC.OS.mydat.out <- rcorr.cens(predict(modRFSRC.OS, newdata = mydat.out)$predicted, Surv(mydat.out$OS, mydat.out$OS_status))
c.f.text(RFSRC.OS.mydat.out)

# Survival Forest for PFS
modRFSRC.PFS <- rfsrc(Surv(PFS, PFS_status) ~ EBVDNA + stage + treat + Tv + Lv, data = mydat, ntree=500)
RFSRC.PFS.mydat <- rcorr.cens(predict(modRFSRC.PFS)$predicted, Surv(mydat$PFS, mydat$PFS_status))
c.f.text(RFSRC.PFS.mydat)
RFSRC.PFS.mydat.val <- rcorr.cens(predict(modRFSRC.PFS, newdata = mydat.val)$predicted, Surv(mydat.val$PFS, mydat.val$PFS_status))
c.f.text(RFSRC.PFS.mydat.val)
RFSRC.PFS.mydat.out <- rcorr.cens(predict(modRFSRC.PFS, newdata = mydat.out)$predicted, Surv(mydat.out$PFS, mydat.out$PFS_status))
c.f.text(RFSRC.PFS.mydat.out)

x <- predictSurvProb(modRFSRC.OS, newdata = mydat.val, time=(1:120))


### 4.计算AUPRC
### PFS
# PFS training
my.base.line.1 <- table(mydat$PFS_status)[2] / sum(table(mydat$PFS_status))
pr.1 <- pr.curve(scores.class0=predict(modRFSRC.PFS)$predicted[mydat$PFS_status==1],
                 scores.class1=predict(modRFSRC.PFS)$predicted[mydat$PFS_status==0], curve=T)
plot(pr.1,main="training set PR Curves",auc.main=FALSE, color = 2, add = FALSE)
lines(c(0,1),rep(my.base.line.1,2), lty=2, col="grey", lwd=3)
pr.1
# PFS val
my.base.line.2 <- table(mydat.val$PFS_status)[2] / sum(table(mydat.val$PFS_status))
pr.2 <- pr.curve(scores.class0=predict(modRFSRC.PFS, newdata = mydat.val)$predicted[mydat.val$PFS_status==1],
                 scores.class1=predict(modRFSRC.PFS, newdata = mydat.val)$predicted[mydat.val$PFS_status==0], curve=T)
plot(pr.2,main="validation set PR Curves",auc.main=FALSE, color = 2, add = FALSE)
lines(c(0,1),rep(my.base.line.2,2), lty=2, col="grey", lwd=3)
pr.2
# PFS out
my.base.line.3 <- table(mydat.out$PFS_status)[2] / sum(table(mydat.out$PFS_status))
pr.3 <- pr.curve(scores.class0=predict(modRFSRC.PFS, newdata = mydat.out)$predicted[mydat.out$PFS_status==1],
                 scores.class1=predict(modRFSRC.PFS, newdata = mydat.out)$predicted[mydat.out$PFS_status==0], curve=T)
plot(pr.3,main="out set PR Curves",auc.main=FALSE, color = 2, add = FALSE)
lines(c(0,1),rep(my.base.line.3,2), lty=2, col="grey", lwd=3)
pr.3
### OS
# OS training
my.base.line.1 <- table(mydat$OS_status)[2] / sum(table(mydat$OS_status))
pr.1 <- pr.curve(scores.class0=predict(modRFSRC.OS)$predicted[mydat$OS_status==1],
                 scores.class1=predict(modRFSRC.OS)$predicted[mydat$OS_status==0], curve=T)
plot(pr.1,main="training set PR Curves",auc.main=FALSE, color = 2, add = FALSE)
lines(c(0,1),rep(my.base.line.1,2), lty=2, col="grey", lwd=3)
pr.1
# OS val
my.base.line.2 <- table(mydat.val$OS_status)[2] / sum(table(mydat.val$OS_status))
pr.2 <- pr.curve(scores.class0=predict(modRFSRC.OS, newdata = mydat.val)$predicted[mydat.val$OS_status==1],
                 scores.class1=predict(modRFSRC.OS, newdata = mydat.val)$predicted[mydat.val$OS_status==0], curve=T)
plot(pr.2,main="validation set PR Curves",auc.main=FALSE, color = 2, add = FALSE)
lines(c(0,1),rep(my.base.line.2,2), lty=2, col="grey", lwd=3)
pr.2
# OS out
my.base.line.3 <- table(mydat.out$OS_status)[2] / sum(table(mydat.out$OS_status))
pr.3 <- pr.curve(scores.class0=predict(modRFSRC.OS, newdata = mydat.out)$predicted[mydat.out$OS_status==1],
                 scores.class1=predict(modRFSRC.OS, newdata = mydat.out)$predicted[mydat.out$OS_status==0], curve=T)
plot(pr.3,main="out set PR Curves",auc.main=FALSE, color = 2, add = FALSE)
lines(c(0,1),rep(my.base.line.3,2), lty=2, col="grey", lwd=3)
pr.3





####################  [my round 3]  ############################################

# set.seed(1954613.331)

{ library(pec)
  library("mfp")
  library("survMisc")
  library("Hmisc")
  library("compareC")
  library("rms")
  library(sampling)
  library(survivalROC)
  library(survAUC)
  library(pROC)
  library(PRROC)
  library(randomForestSRC)
  library("survminer")
  c.f.text <- function(c.f){
    c.f.cindex <- max(c.f[1], 1-c.f[1])
    c.f.SE.196 <- 1.96*c.f[3]/2
    c.f.value <- round(c(c.f.cindex,max(c.f.cindex-c.f.SE.196,0),min(c.f.cindex+c.f.SE.196,1)),3)
    c.f.tex <- paste0(c.f.value[1], "(", c.f.value[2], "-", c.f.value[3], ")")
    return(c.f.tex)}
  my.sens.spec <- function(a,b,c,y,lp,cutoff=0.7,cutoff2=0.6){
    x <- a;x2 <- b
    a <- a[x>cutoff & x2>cutoff2]
    b <- b[x>cutoff & x2>cutoff2]
    c <- c[x>cutoff & x2>cutoff2]
    yue <- a+b
    my.max.id <- which(yue == max(yue))
    my.conf.matr <- table(y, lp>c[my.max.id])
    e1 <- my.conf.matr[2,2]
    n1 <- sum(my.conf.matr[2,])
    p1 <- e1 / n1
    sp1 <- sqrt(p1*(1-p1)/n1)
    text1 <- paste0("sens=",round(p1,3),"(",round(p1-1.96*sp1,3),"-",round(p1+1.96*sp1,3),")")
    e2 <- my.conf.matr[1,1]
    n2 <- sum(my.conf.matr[1,])
    p2 <- e2 / n2
    sp2 <- sqrt(p2*(1-p2)/n2)
    text2 <- paste0("spec=",round(p2,3),"(",round(p2-1.96*sp2,3),"-",round(p2+1.96*sp2,3),")")
    text3 <- paste0("thresholds=",c[my.max.id])
    outcome <- list()
    outcome$text <- c(text1, text2,text3)
    outcome$sens <- paste0(round(p1,3),"(",round(p1-1.96*sp1,3),"-",round(p1+1.96*sp1,3),")")
    outcome$spec <- paste0(round(p2,3),"(",round(p2-1.96*sp2,3),"-",round(p2+1.96*sp2,3),")")
    outcome$thershold <- c[my.max.id]
    outcome$conf.mat <- my.conf.matr
    return(outcome)
  }
}


# setwd("C:\\Users\\35578\\Desktop\\肿瘤cox\\新数据")
setwd("//Users//anchorage//Desktop//2021-07-28_R")

# 读入数据
mydat0 <- read.csv("1640RDD_Version2.csv")
valdat1 <-read.csv("1val_DG.csv")
valdat2 <-read.csv("1val_FS.csv")

valdat1.x <- valdat1[,1:39]
names(valdat1.x) <- names(valdat2)
mydat.out <- rbind(valdat1.x, valdat2)

mydat0$TvLv <- mydat0$Tv + mydat0$Lv
y1.time <- mydat0$OS
y1.status <- mydat0$OS_status
testvar.all <- c("treat","Tv","Lv","TvLv","EBVDNA","T","N","stage","age","EA","VCA")
mydat0$T <- factor(as.character(mydat0$T),levels= c("1","2","3","4"), labels = c("1","2","3","4"))
mydat0$N <- factor(as.character(mydat0$N),levels= c("0","1","2","3"), labels = c("0","1","2","3"))
mydat0$stage <- factor(as.character(mydat0$stage),levels= c("2","3","4"), labels = c("2","3","4"))
mydat0$treat <- factor(as.character(mydat0$treat),levels= c("1","2"), labels = c("1","2"))
mydat.out$stage <- factor(as.character(mydat.out$stage),levels= c("2","3","4"), labels = c("2","3","4"))
mydat.out$treat <- factor(as.character(mydat.out$treat),levels= c("1","2"), labels = c("1","2"))

# seed 
# 1954613.331 X
# 1034802.415 X
# 1745079.908 400 20
# 1398881.241 600 30
my.max.seed <- 1398881.241
m.ntree <- 600 # 树数
m.nodesize <- 30   # 最小节点数

outcome.final <- data.frame(seed=my.max.seed, ntree=m.ntree, nodeside=m.nodesize, model="full")

# 抽样生成数据
set.seed(my.max.seed)
sub_train <- strata(mydat0, stratanames = "OS_status", size = c(1075,74), method = "srswor")
mydat <- mydat0[sub_train$ID_unit,]  # 70%
mydat.val.0 <- mydat0[-sub_train$ID_unit,]
table(mydat.val.0$OS_status)
sub_train.x <- strata(mydat.val.0, stratanames = "OS_status", size = c(306,20), method = "srswor")
mydat.val <- mydat.val.0[-sub_train.x$ID_unit,] # 10%
mydat.test <- mydat.val.0[sub_train.x$ID_unit,]   # 20%

# 定义超参数

m.t <- expand.grid(m.ntree,m.nodesize)
my.j.len <- nrow(m.t)
# 遍历超参数列表，寻找最优参数（validation中cindex最大者）
temp.j.cindex <- numeric(my.j.len)
temp.j.ctext <- character(my.j.len)
t.now <- Sys.time()
for (j in 1:nrow(m.t)) {
  print(paste0("[",j,"/",my.j.len,"(para)]","[",round(as.numeric(Sys.time() - t.now),1),"s]"))
  
  # 1.model
  # Survival Forest for OS(Not need here)
  # modRFSRC.OS <- rfsrc(Surv(OS, OS_status) ~ EBVDNA + stage + treat + Tv + Lv + gender + age, data = mydat, ntree=m.t[j,1], nodesize=m.t[j,2])
  # Survival Forest for PFS
  modRFSRC.PFS <- rfsrc(Surv(PFS, PFS_status) ~ EBVDNA + stage + treat + Tv + Lv + gender + age, data = mydat, ntree=m.t[j,1], nodesize=m.t[j,2])
  # 2.calculate PFS validation c-index
  RFSRC.PFS.mydat.val <- rcorr.cens(predict(modRFSRC.PFS, newdata = mydat.val)$predicted, Surv(mydat.val$PFS, mydat.val$PFS_status))
  temp.j.cindex[j] <- max(RFSRC.PFS.mydat.val[1],(1-RFSRC.PFS.mydat.val[1]))
  temp.j.ctext[j] <- c.f.text(RFSRC.PFS.mydat.val)
}
opt.j <- which(temp.j.cindex==max(temp.j.cindex))[1]

# 记录超参数
opt.ntree <- m.t[opt.j,1]
opt.nodesize <- m.t[opt.j,2]
PFS.cindex.val <- temp.j.ctext[opt.j]
# not need now
# valid.mat <- matrix(data=NA, nrow = length(m.ntree), ncol = length(m.nodesize))
# for (j in 1:nrow(m.t)) {
#   j.id.list <- expand.grid(seq_len(length(m.ntree)),seq_len(length(m.nodesize)))
#   valid.mat[j.id.list[j,1], j.id.list[j,2]] <- temp.j.cindex[j]
# }
# rownames(valid.mat) <- m.ntree
# colnames(valid.mat) <- m.nodesize

outcome.final$cindex.PFS.val <- PFS.cindex.val

# 使用超参数重新训练模型
mydat.x2 <- rbind(mydat, mydat.val)
# Survival Forest for OS
modRFSRC.OS <- rfsrc(Surv(OS, OS_status) ~ EBVDNA + stage + treat + Tv + Lv + gender + age, data = mydat.x2, ntree=m.t[opt.j,1], nodesize=m.t[opt.j,2],var.used = "all.trees")
# Survival Forest for PFS
modRFSRC.PFS <- rfsrc(Surv(PFS, PFS_status) ~ EBVDNA + stage + treat + Tv + Lv + gender + age, data = mydat.x2, ntree=m.t[opt.j,1], nodesize=m.t[opt.j,2],var.used = "all.trees")

# 权重计算
modRFSRC.OS.imp <- vimp(modRFSRC.OS, importance = "permute", block.size = 10)$importance
modRFSRC.PFS.imp <- vimp(modRFSRC.PFS, importance = "permute", block.size = 10)$importance
modRFSRC.OS$var.used
modRFSRC.PFS$var.used
modRFSRC.OS$var.used / sum(modRFSRC.OS$var.used)
modRFSRC.PFS$var.used / sum(modRFSRC.PFS$var.used)

# model 1
modRFSRC.OS.m1 <- rfsrc(Surv(OS, OS_status) ~ stage, data = mydat.x2, ntree=m.t[opt.j,1], nodesize=m.t[opt.j,2])
modRFSRC.PFS.m1 <- rfsrc(Surv(PFS, PFS_status) ~ stage, data = mydat.x2, ntree=m.t[opt.j,1], nodesize=m.t[opt.j,2])
# model 2
modRFSRC.OS.m2 <- rfsrc(Surv(OS, OS_status) ~ EBVDNA + stage + treat + gender + age, data = mydat.x2, ntree=m.t[opt.j,1], nodesize=m.t[opt.j,2])
modRFSRC.PFS.m2 <- rfsrc(Surv(PFS, PFS_status) ~ EBVDNA + stage + treat +  gender + age, data = mydat.x2, ntree=m.t[opt.j,1], nodesize=m.t[opt.j,2])

#modRFSRC.OS <- modRFSRC.OS.m1
#modRFSRC.PFS <- modRFSRC.PFS.m1
#modRFSRC.OS <- modRFSRC.OS.m2
#modRFSRC.PFS <- modRFSRC.PFS.m2


###  模型评价
# 0.计算预测值
lp.PFS.test <- predict(modRFSRC.PFS, newdata = mydat.test)$predicted
lp.PFS.out <- predict(modRFSRC.PFS, newdata = mydat.out)$predicted
lp.OS.test <- predict(modRFSRC.OS, newdata = mydat.test)$predicted
lp.OS.out <- predict(modRFSRC.OS, newdata = mydat.out)$predicted

# 1. c-index
RFSRC.PFS.mydat.test <- rcorr.cens(lp.PFS.test, Surv(mydat.test$PFS, mydat.test$PFS_status))
RFSRC.PFS.mydat.out <- rcorr.cens(lp.PFS.out, Surv(mydat.out$PFS, mydat.out$PFS_status))
RFSRC.OS.mydat.test <- rcorr.cens(lp.OS.test, Surv(mydat.test$OS, mydat.test$OS_status))
RFSRC.OS.mydat.out <- rcorr.cens(lp.OS.out, Surv(mydat.out$OS, mydat.out$OS_status))

outcome.final$cindex.PFS.test <- c.f.text(RFSRC.PFS.mydat.test)
outcome.final$cindex.PFS.out <- c.f.text(RFSRC.PFS.mydat.out)
outcome.final$cindex.OS.test <- c.f.text(RFSRC.OS.mydat.test)
outcome.final$cindex.OS.out <- c.f.text(RFSRC.OS.mydat.out)

# 以下，令5年PFS作为二分类结局处理
my.cutage <- 60
mydat.x2$PFS5y <- ((mydat.x2$PFS_status==1) & (mydat.x2$PFS <= my.cutage))*1
mydat.test$PFS5y <- ((mydat.test$PFS_status==1) & (mydat.test$PFS <= my.cutage))*1
mydat.out$PFS5y <- ((mydat.out$PFS_status==1) & (mydat.out$PFS <= my.cutage))*1

mydat.x2$OS5y <- ((mydat.x2$OS_status==1) & (mydat.x2$OS <= my.cutage))*1
mydat.test$OS5y <- ((mydat.test$OS_status==1) & (mydat.test$OS <= my.cutage))*1
mydat.out$OS5y <- ((mydat.out$OS_status==1) & (mydat.out$OS <= my.cutage))*1
# 2.AUPRC - PFS
prc.train <- pr.curve(scores.class0=predict(modRFSRC.PFS)$predicted[mydat.x2$PFS5y==1],
                      scores.class1=predict(modRFSRC.PFS)$predicted[mydat.x2$PFS5y==0], curve=T)
prc.test <- pr.curve(scores.class0=lp.PFS.test[mydat.test$PFS5y==1],
                     scores.class1=lp.PFS.test[mydat.test$PFS5y==0], curve=T)
prc.test.m1 <- pr.curve(scores.class0=predict(modRFSRC.PFS.m1, newdata = mydat.test)$predicted[mydat.test$PFS5y==1],
                        scores.class1=predict(modRFSRC.PFS.m1, newdata = mydat.test)$predicted[mydat.test$PFS5y==0], curve=T)
prc.test.m2 <- pr.curve(scores.class0=predict(modRFSRC.PFS.m2, newdata = mydat.test)$predicted[mydat.test$PFS5y==1],
                        scores.class1=predict(modRFSRC.PFS.m2, newdata = mydat.test)$predicted[mydat.test$PFS5y==0], curve=T)
prc.out <- pr.curve(scores.class0=lp.PFS.out[mydat.out$PFS5y==1],
                    scores.class1=lp.PFS.out[mydat.out$PFS5y==0], curve=T)
prc.out.m1 <- pr.curve(scores.class0=predict(modRFSRC.PFS.m1, newdata = mydat.out)$predicted[mydat.out$PFS5y==1],
                       scores.class1=predict(modRFSRC.PFS.m1, newdata = mydat.out)$predicted[mydat.out$PFS5y==0], curve=T)
prc.out.m2 <- pr.curve(scores.class0=predict(modRFSRC.PFS.m2, newdata = mydat.out)$predicted[mydat.out$PFS5y==1],
                       scores.class1=predict(modRFSRC.PFS.m2, newdata = mydat.out)$predicted[mydat.out$PFS5y==0], curve=T)

# my.base.line.train <- table(mydat.x2$PFS5y)[2] / sum(table(mydat.x2$PFS5y))
my.base.line.test <- table(mydat.test$PFS5y)[2] / sum(table(mydat.test$PFS5y))
my.base.line.out <- table(mydat.out$PFS5y)[2] / sum(table(mydat.out$PFS5y))

plot(prc.test,  main=paste0("PR Curves for ",round(my.cutage/12)," year PFS"), auc.main=FALSE, color = 2, add = FALSE)
plot(prc.test.m1 , color = 3, add = TRUE)
plot(prc.test.m2 , color = 4, add = TRUE)
lines(c(0,1),rep(my.base.line.test,2), lty=2, col=5, lwd=3)
legend("topright", inset=.05, title="Model", c(paste0("full model:",round(prc.test$auc.davis.goadrich,3)),
                                               paste0("stage only model:",round(prc.test.m1$auc.davis.goadrich,3)),
                                               paste0("no TvLv model:",round(prc.test.m2$auc.davis.goadrich,3)),
                                               paste0("reference:",round(my.base.line.test,3))),
       lty=c(1,1,1,2),lwd=3 , col=c(2,3,4,5))

plot(prc.out,  main=paste0("PR Curves for ",round(my.cutage/12)," year PFS"), auc.main=FALSE, color = 2, add = FALSE)
plot(prc.out.m1 , color = 3, add = TRUE)
plot(prc.out.m2 , color = 4, add = TRUE)
lines(c(0,1),rep(my.base.line.out,2), lty=2, col=5, lwd=3)
legend("topright", inset=.05, title="Model", c(paste0("full model:",round(prc.out$auc.davis.goadrich,3)),
                                               paste0("stage only model:",round(prc.out.m1$auc.davis.goadrich,3)),
                                               paste0("no TvLv model:",round(prc.out.m2$auc.davis.goadrich,3)),
                                               paste0("reference:",round(my.base.line.test,3))),
       lty=c(1,1,1,2),lwd=3 , col=c(2,3,4,5))


# plot(prc.train, main=paste0("PR Curves for ",round(my.cutage/12)," year PFS"), auc.main=FALSE, color = 2, add = FALSE)
# plot(prc.test, color = 3, add = TRUE)
# plot(prc.out, color = 4, add = TRUE)
# lines(c(0,1),rep(my.base.line.train,2), lty=2, col=2, lwd=3)
# lines(c(0,1),rep(my.base.line.test,2), lty=2, col=3, lwd=3)
# lines(c(0,1),rep(my.base.line.out,2), lty=2, col=4, lwd=3)
# legend("topright", inset=.05, title="Model", c(paste0("training:",round(prc.train$auc.davis.goadrich,3)),
#                                                paste0("test:",round(prc.test$auc.davis.goadrich,3)),
#                                                paste0("out:",round(prc.out$auc.davis.goadrich,3)),
#                                                paste0("reference line-training:",round(my.base.line.train,3)),
#                                                paste0("reference line-test:",round(my.base.line.test,3)),
#                                                paste0("reference line-out:",round(my.base.line.out,3))),
#        lty=c(1,1,1,2,2,2),lwd=3 , col=c(2,3,4,2,3,4))


outcome.final$prc.PFS.train <- round(prc.train$auc.davis.goadrich,3)
outcome.final$prc.PFS.test <- round(prc.test$auc.davis.goadrich,3)
outcome.final$prc.PFS.out <- round(prc.out$auc.davis.goadrich,3)

# 3.灵敏度和特异度
# pfs
outcome.1 <- roc(response=mydat.test$PFS5y,predictor = lp.PFS.test)
PFS.sens.spec.test <- my.sens.spec(outcome.1$sensitivities,outcome.1$specificities,outcome.1$thresholds,mydat.test$PFS5y,
                                   lp.PFS.test,0.62)
outcome.2 <- roc(response=mydat.out$PFS5y,predictor = lp.PFS.out)
PFS.sens.spec.out <- my.sens.spec(outcome.2$sensitivities,outcome.2$specificities,outcome.2$thresholds,mydat.out$PFS5y,
                                  lp.PFS.out,0.5)
# os
outcome.3 <- roc(response=mydat.test$OS5y,predictor = lp.OS.test)
OS.sens.spec.test <- my.sens.spec(outcome.3$sensitivities,outcome.3$specificities,outcome.3$thresholds,mydat.test$OS5y,
                                  lp.OS.test,0.5,0.7)
outcome.4 <- roc(response=mydat.out$OS5y,predictor = lp.OS.out)
OS.sens.spec.out <- my.sens.spec(outcome.4$sensitivities,outcome.4$specificities,outcome.4$thresholds,mydat.out$OS5y,
                                 lp.OS.out,0.61)

outcome.final$sens.PFS.test <- PFS.sens.spec.test$sens
outcome.final$sens.PFS.out <- PFS.sens.spec.out$sens
outcome.final$sens.OS.test <- OS.sens.spec.test$sens
outcome.final$sens.OS.out <- OS.sens.spec.out$sens
outcome.final$spec.PFS.test <- PFS.sens.spec.test$spec
outcome.final$spec.PFS.out <- PFS.sens.spec.out$spec
outcome.final$spec.OS.test <- OS.sens.spec.test$spec
outcome.final$spec.OS.out <- OS.sens.spec.out$spec

# 4.F值
p.ci <- function(F.u,F.d){
  F.value <- F.u/F.d 
  sp <- sqrt(F.value*(1-F.value)/F.d)
  F.text <- paste0(round(F.value,3),"(",round(F.value-1.96*sp,3),"-",round(F.value+1.96*sp,3),")")
  return(F.text)
}
my.F.test <- function(conf.mat){
  TP <- conf.mat[2,2]
  FP <- conf.mat[1,2]
  FN <- conf.mat[2,1]
  F.u <- 2*TP
  F.d <- 2*TP+FP+FN
  F1 <- p.ci(F.u,F.d)
  F.u <- 1.5*TP
  F.d <- 1.25*TP+0.25*FN+FP
  F0.5 <- p.ci(F.u,F.d)
  F.u <- 5*TP
  F.d <- 5*TP+4*FN+FP
  F2 <- p.ci(F.u,F.d)
  return(list(F1=F1,F0.5=F0.5,F2=F2))
}
PFS.F.test <- my.F.test(PFS.sens.spec.test$conf.mat)
PFS.F.out <- my.F.test(PFS.sens.spec.out$conf.mat)
OS.F.test <- my.F.test(OS.sens.spec.test$conf.mat)
OS.F.out <- my.F.test(OS.sens.spec.out$conf.mat)

outcome.final$F1.PFS.test <- PFS.F.test$F1
outcome.final$F1.PFS.out <- PFS.F.out$F1
outcome.final$F1.OS.test <- OS.F.test$F1
outcome.final$F1.OS.out <- OS.F.out$F1
outcome.final$F0.5.PFS.test <- PFS.F.test$F0.5
outcome.final$F0.5.PFS.out <- PFS.F.out$F0.5
outcome.final$F0.5.OS.test <- OS.F.test$F0.5
outcome.final$F0.5.OS.out <- OS.F.out$F0.5
outcome.final$F2.PFS.test <- PFS.F.test$F2
outcome.final$F2.PFS.out <- PFS.F.out$F2
outcome.final$F2.OS.test <- OS.F.test$F2
outcome.final$F2.OS.out <- OS.F.out$F2

# 5.Log-rank 及其 p value
# PFS
mydat.test$lr.PFS.group <- (lp.PFS.test > median(lp.PFS.test))*1
mydat.out$lr.PFS.group <- (lp.PFS.out > median(lp.PFS.out))*1
PFS.lr.test <- survdiff(Surv(PFS, PFS_status) ~ lr.PFS.group, mydat.test)
outcome.final$lr.chi.PFS.test <- PFS.lr.test$chisq
outcome.final$lr.p.PFS.test <- 1-pchisq(outcome.final$lr.chi.PFS.test,1)
PFS.lr.out <- survdiff(Surv(PFS, PFS_status) ~ lr.PFS.group, mydat.out)
outcome.final$lr.chi.PFS.out <- PFS.lr.out$chisq
outcome.final$lr.p.PFS.out <- 1-pchisq(outcome.final$lr.chi.PFS.out,1)
# OS
mydat.test$lr.OS.group <- (lp.OS.test > median(lp.OS.test))*1
mydat.out$lr.OS.group <- (lp.OS.out > median(lp.OS.out))*1
OS.lr.test <- survdiff(Surv(OS, OS_status) ~ lr.OS.group, mydat.test)
outcome.final$lr.chi.OS.test <- OS.lr.test$chisq
outcome.final$lr.p.OS.test <- 1-pchisq(outcome.final$lr.chi.OS.test,1)
OS.lr.out <- survdiff(Surv(OS, OS_status) ~ lr.OS.group, mydat.out)
outcome.final$lr.chi.OS.out <- OS.lr.out$chisq
outcome.final$lr.p.OS.out <- 1-pchisq(outcome.final$lr.chi.OS.out,1)
# 绘图
fit.PFS.test <- survfit(Surv(PFS, PFS_status) ~ lr.PFS.group, mydat.test)
fit.PFS.out <- survfit(Surv(PFS, PFS_status) ~ lr.PFS.group, mydat.out)
fit.OS.test <- survfit(Surv(OS, OS_status) ~ lr.OS.group, mydat.test)
fit.OS.out <- survfit(Surv(OS, OS_status) ~ lr.OS.group, mydat.out)

ggsurvplot(fit.PFS.test,legend.labs=c("low","high"), legend.title="group")
ggsurvplot(fit.PFS.out,legend.labs=c("low","high"), legend.title="group")
ggsurvplot(fit.OS.test,legend.labs=c("low","high"), legend.title="group")
ggsurvplot(fit.OS.out,legend.labs=c("low","high"), legend.title="group")

fit.x <- survfit(Surv(PFS, PFS_status) ~ stage, mydat[mydat$treat==2,])
ggsurvplot(fit.x)

#### careful!!!!!!!!

# outcome.final.1 <- outcome.final
# outcome.final.2 <- outcome.final
# outcome.final.3 <- outcome.final

outcome.final.full <- rbind(outcome.final.1,outcome.final.2,outcome.final.3)
outcome.final.full$model[2] <- "only.stage"
outcome.final.full$model[3] <- "not.tv.lv"

# cindex比较
outcome.final.full$test.cindex.OS.out <- outcome.final.full$test.cindex.OS.test <-
  outcome.final.full$test.cindex.PFS.test <- outcome.final.full$test.cindex.PFS.out <- 1
outcome.final.full$test.cindex.PFS.test[2] <- round(compareC(mydat.test$PFS, mydat.test$PFS_status, 
                                                             predict(modRFSRC.PFS, newdata = mydat.test)$predicted, 
                                                             predict(modRFSRC.PFS.m1, newdata = mydat.test)$predicted)$pval,5)
outcome.final.full$test.cindex.PFS.test[3] <- round(compareC(mydat.test$PFS, mydat.test$PFS_status, 
                                                             predict(modRFSRC.PFS, newdata = mydat.test)$predicted, 
                                                             predict(modRFSRC.PFS.m2, newdata = mydat.test)$predicted)$pval,5)
outcome.final.full$test.cindex.PFS.out[2] <- round(compareC(mydat.out$PFS, mydat.out$PFS_status, 
                                                            predict(modRFSRC.PFS, newdata = mydat.out)$predicted, 
                                                            predict(modRFSRC.PFS.m1, newdata = mydat.out)$predicted)$pval,5)
outcome.final.full$test.cindex.PFS.out[3] <- round(compareC(mydat.out$PFS, mydat.out$PFS_status, 
                                                            predict(modRFSRC.PFS, newdata = mydat.out)$predicted,
                                                            predict(modRFSRC.PFS.m2, newdata = mydat.out)$predicted)$pval,5)
outcome.final.full$test.cindex.OS.test[2] <- round(compareC(mydat.test$OS, mydat.test$OS_status,
                                                            predict(modRFSRC.OS, newdata = mydat.test)$predicted,
                                                            predict(modRFSRC.OS.m1, newdata = mydat.test)$predicted)$pval,5)
outcome.final.full$test.cindex.OS.test[3] <- round(compareC(mydat.test$OS, mydat.test$OS_status, 
                                                            predict(modRFSRC.OS, newdata = mydat.test)$predicted,
                                                            predict(modRFSRC.OS.m2, newdata = mydat.test)$predicted)$pval,5)
outcome.final.full$test.cindex.OS.out[2] <- round(compareC(mydat.out$OS, mydat.out$OS_status,
                                                           predict(modRFSRC.OS, newdata = mydat.out)$predicted, 
                                                           predict(modRFSRC.OS.m1, newdata = mydat.out)$predicted)$pval,5)
outcome.final.full$test.cindex.OS.out[3] <- round(compareC(mydat.out$OS, mydat.out$OS_status, 
                                                           predict(modRFSRC.OS, newdata = mydat.out)$predicted, 
                                                           predict(modRFSRC.OS.m2, newdata = mydat.out)$predicted)$pval,5)

t(outcome.final.full)

write.csv(outcome.final.full,"outcome.final.full.csv", row.names = F)

###  模型应用

setwd("//Users//anchorage//Desktop//2021-07-28_R")

my.i <- 4
par(mfrow=c(3,3), mar=c(my.i,my.i,my.i,0), mgp=c(1.3,0.6,0),
    xaxs="i", yaxs="i")

{
my.gender <- 1
my.age <- 50
my.EBVDNA <- 6000
my.stage <- 3
my.Tv <- c(50, 70, 250)
my.Lv <- c(25, 30, 60)
}

for (i in 1:3) {
  for (j in 1:3) {
    # plot predict curve
    new.data <- data.frame(gender=my.gender,
                           age=my.age,
                           EBVDNA=my.EBVDNA,
                           stage=my.stage,
                           Tv=my.Tv[j],
                           Lv=my.Lv[i])
    new.data.treat1 <- new.data.treat2 <- new.data
    temp.treat <- factor(c(1,2), levels = c(1,2))
    temp.stage <- factor(c(2,3,4), levels = c(2,3,4))
    new.data.treat1$stage <- temp.stage[new.data.treat1$stage==temp.stage]
    new.data.treat2$stage <- temp.stage[new.data.treat2$stage==temp.stage]
    new.data.treat1$treat <- temp.treat[1]
    new.data.treat2$treat <- temp.treat[2]

    # PFS
    p.treat.1 <- predictSurvProb(modRFSRC.PFS, newdata = new.data.treat1, time=seq(1,60,0.1))
    p.treat.2 <- predictSurvProb(modRFSRC.PFS, newdata = new.data.treat2, time=seq(1,60,0.1))
    vec.len <- length(p.treat.1)
    plot(seq(1,60,0.1),p.treat.2,ylim=c(0,1),type="l",lwd = 2, lty=1,
         col="red",main="PFS curves",xlab="Time",ylab="S(t|X)")
    polygon(c(seq(1,60,0.1),rev(seq(1,60,0.1))), c(p.treat.2,rep(0,vec.len)),
            xpd = FALSE, col = "orange", lwd = 1, border = NA)
    lines(seq(1,60,0.1),p.treat.2,ylim=c(0,1),type="l",lwd = 2, lty=1,
          col="red",main="Survival curves",xlab="Time",ylab="S(t|X)")
    polygon(c(seq(1,60,0.1),rev(seq(1,60,0.1))), c(p.treat.1,rep(0,vec.len)),
            xpd = FALSE, col = "#00C957", lwd = 1, border = NA)
    lines(seq(1,60,0.1),p.treat.1,ylim=c(0,1),type="l",lwd = 2, lty=1,
          col="#3D9140",main="PFS curves",xlab="Time",ylab="S(t|X)")
    rate.text.PFS <- paste(round((sum(p.treat.2)/sum(p.treat.1)-1)*100,2),"%")
    legend("bottomleft",inset=c(0.04,0.03),bg="transparent", bty="n",title=paste0("treatment ","[Rate=",rate.text.PFS,"]"), c("treatment=2", "treatment=1"),
           lty=c(1,1),lwd=c(2,2) , col=c("red","#3D9140"))
  }
}

for (i in 1:3) {
  for (j in 1:3) {
    # plot predict curve
    new.data <- data.frame(gender=my.gender,
                           age=my.age,
                           EBVDNA=my.EBVDNA,
                           stage=my.stage,
                           Tv=my.Tv[j],
                           Lv=my.Lv[i])
    new.data.treat1 <- new.data.treat2 <- new.data
    temp.treat <- factor(c(1,2), levels = c(1,2))
    temp.stage <- factor(c(2,3,4), levels = c(2,3,4))
    new.data.treat1$stage <- temp.stage[new.data.treat1$stage==temp.stage]
    new.data.treat2$stage <- temp.stage[new.data.treat2$stage==temp.stage]
    new.data.treat1$treat <- temp.treat[1]
    new.data.treat2$treat <- temp.treat[2]
    
    # PFS
    p.treat.1 <- predict(modRFSRC.PFS, newdata = new.data.treat1)$survival[1:60]
    p.treat.2 <- predict(modRFSRC.PFS, newdata = new.data.treat2)$survival[1:60]
    vec.len <- length(p.treat.1)
    plot(seq(1,60,1),p.treat.2,ylim=c(0,1),type="l",lwd = 2, lty=1,
         col="red",main="PFS curves",xlab="Time",ylab="S(t|X)")
    polygon(c(seq(1,60,1),rev(seq(1,60,1))), c(p.treat.2,rep(0,vec.len)), 
            xpd = FALSE, col = "orange", lwd = 1, border = NA)
    lines(seq(1,60,1),p.treat.2,ylim=c(0,1),type="l",lwd = 2, lty=1,
          col="red",main="Survival curves",xlab="Time",ylab="S(t|X)")
    polygon(c(seq(1,60,1),rev(seq(1,60,1))), c(p.treat.1,rep(0,vec.len)), 
            xpd = FALSE, col = "#00C957", lwd = 1, border = NA)
    lines(seq(1,60,1),p.treat.1,ylim=c(0,1),type="l",lwd = 2, lty=1,
          col="#3D9140",main="PFS curves",xlab="Time",ylab="S(t|X)")
    rate.text.PFS <- paste(round((sum(p.treat.2)/sum(p.treat.1)-1)*100,2),"%")
    legend("bottomleft",inset=c(0.04,0.03),bg="transparent", bty="n",title=paste0("treatment ","[Rate=",rate.text.PFS,"]"), c("treatment=2", "treatment=1"),
           lty=c(1,1),lwd=c(2,2) , col=c("red","#3D9140"))
  }
}





{
new.data <- data.frame(gender=my.gender,
                       age=my.age,
                       EBVDNA=my.EBVDNA,
                       stage=3,
                       Tv=my.Tv[j],
                       Lv=my.Lv[i])
new.data.treat1 <- new.data.treat2 <- new.data
temp.treat <- factor(c(1,2), levels = c(1,2))
temp.stage <- factor(c(2,3,4), levels = c(2,3,4))
new.data.treat1$stage <- temp.stage[new.data.treat1$stage==temp.stage]
new.data.treat2$stage <- temp.stage[new.data.treat2$stage==temp.stage]
new.data.treat1$treat <- temp.treat[1]
new.data.treat2$treat <- temp.treat[2]
}

predict(modRFSRC.PFS, newdata = new.data.treat1)$chf
predict(modRFSRC.PFS, newdata = new.data.treat1)$survival

head(predict(modRFSRC.PFS, newdata = new.data.treat1)$predicted)

plot.variable(modRFSRC.PFS)

table(mydat$gender, mydat$stage, mydat$PFS_status)
table(mydat$stage, mydat$PFS_status, mydat$gender)

for (i in 1:3) {
  for (j in 1:3) {
    # plot predict curve
    new.data <- data.frame(gender=my.gender,
                           age=my.age,
                           EBVDNA=my.EBVDNA,
                           stage=my.stage,
                           Tv=my.Tv[j],
                           Lv=my.Lv[i])
    new.data.treat1 <- new.data.treat2 <- new.data
    temp.treat <- factor(c(1,2), levels = c(1,2))
    temp.stage <- factor(c(2,3,4), levels = c(2,3,4))
    new.data.treat1$stage <- temp.stage[new.data.treat1$stage==temp.stage]
    new.data.treat2$stage <- temp.stage[new.data.treat2$stage==temp.stage]
    new.data.treat1$treat <- temp.treat[1]
    new.data.treat2$treat <- temp.treat[2]
    
    # OS
    p.treat.1 <- predictSurvProb(modRFSRC.OS, newdata = new.data.treat1, time=seq(1,60,0.1))
    p.treat.2 <- predictSurvProb(modRFSRC.OS, newdata = new.data.treat2, time=seq(1,60,0.1))
    vec.len <- length(p.treat.1)
    plot(seq(1,60,0.1),p.treat.2,ylim=c(0,1),type="l",lwd = 2, lty=1,
         col="red",main="OS curves",xlab="Time",ylab="S(t|X)")
    polygon(c(seq(1,60,0.1),rev(seq(1,60,0.1))), c(p.treat.2,rep(0,vec.len)), 
            xpd = FALSE, col = "orange", lwd = 1, border = NA)
    lines(seq(1,60,0.1),p.treat.2,ylim=c(0,1),type="l",lwd = 2, lty=1,
          col="red",main="OS curves",xlab="Time",ylab="S(t|X)")
    polygon(c(seq(1,60,0.1),rev(seq(1,60,0.1))), c(p.treat.1,rep(0,vec.len)), 
            xpd = FALSE, col = "#00C957", lwd = 1, border = NA)
    lines(seq(1,60,0.1),p.treat.1,ylim=c(0,1),type="l",lwd = 2, lty=1,
          col="#3D9140",main="OS curves",xlab="Time",ylab="S(t|X)")
    rate.text.OS <- paste(round((sum(p.treat.2)/sum(p.treat.1)-1)*100,2),"%")
    legend("bottomleft",inset=c(0.04,0.03),bg="transparent", bty="n",title=paste0("treatment ","[Rate=",rate.text.OS,"]"), c("treatment=2", "treatment=1"),
           lty=c(1,1),lwd=c(2,2) , col=c("red","#3D9140"))
  }
}







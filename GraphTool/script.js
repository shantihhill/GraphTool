console.log("START ALL");

var nodeCnt = 0, edgeCnt = 0;
var edges = [], newEdges = [];
var nodes = [], newNodes = [];
var mapNd = {};

//canvas initialization + constants;
var ndRad = 30, edgeIdealLength = 150, edgePrcIncr = 0.035;
var lineWidth = 3, arcLineWidth = 5, thickArcLineWidth = 14;
var cnvSz = 800, cnv, ctx;
var mX, mY, fX, fY, time = 0, clickTime = 15, directed = 0;
var graphMode = "gravity";
var dirTriLen = 30, zeroLimit = 1e-10, maxInt = Number.MAX_SAFE_INTEGER;
var disWE = 20, randLenInt = 100, textDiffMark = 80;
var inpX = 0, inpY = 0, inpMaxTop = 39, inpMaxLeft = 36, inpBox;
cnv = document.getElementById("myCanvas");
ctx = cnv.getContext("2d");
cnv.width = cnvSz;
cnv.height = cnvSz;
var cx = cnvSz / 2, cy = cnvSz / 2, ct = 0;
var ncF = 0.0008, nnF = 100000, edF = 0.003, fErr = 0.00001, edDistErr = 10;
var ndEffRad = 160, dragF = 0.2, maxVel = 5, dragRate = 0.96; 
var FPS = 100, fpsInterval, now, then, elapsed;

// phone number: 737 223 0769

timeLoop();

updateGraphData();

function drawSmallCircle(x, y, sz) {
	//console.log("am desenat circle");
	ctx.beginPath();
	ctx.moveTo(x, y);
	ctx.arc(x, y, sz, 0, 2 * Math.PI);
	ctx.stroke();
}

function timeLoop() {
	time++;
//	console.log("timpul global: " + time);
	requestAnimationFrame(timeLoop);
}

function swapNodes(a, b) {
	var c = nodes[a].name;
	nodes[a].name = nodes[b].name;
	nodes[b].name = c;
	var c = nodes[a].posX;
	nodes[a].posX = nodes[b].posX;
	nodes[b].posX = c;
	var c = nodes[a].posY;
	nodes[a].posY = nodes[b].posY;
	nodes[b].posY = c;
	var c = nodes[a].vX;
	nodes[a].vX = nodes[b].vX;
	nodes[b].vX = c;
	var c = nodes[a].vY;
	nodes[a].vY = nodes[b].vY;
	nodes[b].vY = c;
}

function mouseOut() {
	console.log("mouse out ba pula");
}

function isNumber(n) { return /^-?[\d.]+(?:e-?\d+)?$/.test(n); }

function distAB(x, y, a, b) {
	return (x - a) * (x - a) + (y - b) * (y - b);
}

function updateInputBox(x0, y0) {
	// 0 -> 0; cnvSz -> 39,36
	inpX = x0 * inpMaxLeft / cnvSz;
	inpY = y0 * inpMaxTop / cnvSz;
	inpBox.style["top"] = inpY + "vw";	
	inpBox.style["left"] = inpX+ "vw";
}

function graphInputUpdate() {
	var txt = "";
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].first	!= undefined)	txt += edges[i].first + " ";
		if (edges[i].second != undefined) txt += edges[i].second + " ";
		if (edges[i].leng != undefined)	txt += edges[i].leng;
		txt += "\n";
	}
	document.getElementById("graphData").value = txt;
}

function addRandomLengths() {
	for (var i = 0; i < edgeCnt; i++) {
		edges[i].leng = parseInt(Math.random() *	randLenInt);
	}
	graphInputUpdate();
}

function sortShuffle() {
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].posX = ndRad + Math.random() * (cnvSz - ndRad);
		nodes[i].posY = Math.random() * (cnvSz - ndRad);
		nodes[i].vX = 0;
		nodes[i].vY = 0;
	}
}

function makeDirected() {
	directed = 1;
}
function makeUndirected() {
	directed = 0;
}

function edgeArcTarget(x0, y0, a0, b0, dis) {
	var c = new Object; 
	if (a0 == "nu") {
		c.t1X = x0 - dis;
		c.t1Y = y0;
		c.t2X = x0 + dis;
		c.t2Y = y0;
		return c;	
	} else if (Math.abs(a0) < zeroLimit) {
		c.t1X = x0;
		c.t1Y = y0 - dis;
		c.t2X = x0;
		c.t2Y = y0 + dis;
		return c;
	}
	var a1 = -1 / a0, b1 = y0 - a1 * x0;
	var qa = (1 + a1 * a1), qb = (2 * a1 * b1 - 2 * x0 - 2 * y0 * a1), qc = (x0 * x0 + y0 * y0 + b1 * b1 - 2 * y0 * b1 - dis * dis);
	var dt = Math.sqrt(Math.abs(qb * qb - 4 * qa * qc));

	c.t1X = (-qb + dt) / (2 * qa);
	c.t1Y = a1 * c.t1X + b1;
	c.t2X = (-qb - dt) / (2 * qa);
	c.t2Y = a1 * c.t2X + b1;
//	console.log("gata target: " + a1 + " " + a0 + "    " + c.t1X + " " + c.t1Y + " " + c.t2X + " " + c.t2Y);
	return c;
}

function drawEdgeArc(i, x0, y0, x1, y1, x2, y2) {
	var dd = Math.sqrt(distAB(x0, y0, x2, y2));
	var x3 = 2 * x1 - x0 / 2 - x2 / 2;
	var y3 = 2 * y1 - y0 / 2 - y2 / 2;
	var mx = (x0 + x2) / 2, my = (y0 + y2) / 2; 
	ctx.beginPath();
	ctx.moveTo(x0, y0);	
	ctx.quadraticCurveTo(x3, y3, x2, y2);
	ctx.stroke();

	if (edges[i].leng != undefined) {
		var sx0 = x0, sy0 = y0, sx2 = x2, sy2 = y2, aux;
		var wordW = ctx.measureText(edges[i].leng).width, wordH = ctx.measureText(edges[i].leng).height;	
		var cX, cY, kX, z = disWE;
		sx0 += edges[i].trdX - mx;
		sy0 += edges[i].trdY - my;
		sx2 += edges[i].trdX - mx;
		sy2 += edges[i].trdY - my;
		if (sx0 > sx2) {
			aux = sx0, sx0 = sx2, sx2 = aux;
			aux = sy0, sy0 = sy2, sy2 = aux;
		}
		
		if (sx0 == sx2) {
				cX = edges[i].trdX;
				cY = edges[i].trdY;
				ctx.textAlign = "center";
		} else if (sy0 == sy2) {
				cX = edges[i].trdX;
				cY = edges[i].trdY;
				ctx.textAlign = "center";
		} else {
			var a1 = (sy2 - sy0) / (sx2 - sx0), b1 = sy0 - a1 * sx0;
			var a0 = -1 / a1, b0 = edges[i].trdY - a0 * edges[i].trdX;
			if (sy0 > sy2) {
				cX = (a1 * z + b1 - b0) / (a0 - a1);
				cY = a0 * cX + b0;
				ctx.textAlign = "right";
				
				var dx = Math.abs(sy0 - sy2), dy = Math.abs(sx0-sx2);
				console.log("dx; " + dx + " dy: " + dy);
				if (dx < dy) {
					if (dx < textDiffMark) {
						dx = textDiffMark - dx;
						cX += wordW / 2 * dx / textDiffMark;
					}
				}
				else if (dy < dx) {
					if (dy < textDiffMark) {
						dy = textDiffMark - dy;
						cX += (wordW / 2 + disWE)  * dy / textDiffMark;	
					}
				}
			} else {
				cX = (b1 - b0 - a1 * z) / (a0 - a1);
				cY = a0 * cX + b0;
				ctx.textAlign = "left";

				var dx = Math.abs(sy0 - sy2), dy = Math.abs(sx0-sx2);
				console.log("dx; " + dx + " dy: " + dy);
				if (dx < dy) {
					if (dx < textDiffMark) {
						dx = textDiffMark - dx;
						cX -= wordW / 2 * dx / textDiffMark;
					}
				}
				else if (dy < dx) {
					if (dy < textDiffMark) {
						dy = textDiffMark - dy;
						cX -= (wordW / 2 + disWE)  * dy / textDiffMark;	
					}
				}
			}
		}	
//		ctx.textAlign = "center";
		ctx.textBaseline = "bottom";
		ctx.fillStyle = document.getElementById("nodeColor").value;
		ctx.fillText(edges[i].leng, cX, cY);
		edges[i].lengX = cX;
		edges[i].lengY = cY;
	}

	if (directed && dd > dirTriLen) {
		var dmx = (cnvSz - 2 * ndRad) * Math.sqrt(2);
		x1 = (x1 + x3) / 2;
		y1 = (y1 + y3) / 2;
		x3 = x1 + (x3 - x1) * dd / dmx;
		y3 = y1 + (y3 - y1) * dd / dmx;

		var dd = Math.sqrt(distAB(x3, y3, x2, y2));
		var fx = x2 + (x3 - x2) * ndRad / dd;	
		var fy = y2 + (y3 - y2) * ndRad / dd;
		var sx = x2 + (x3 - x2) * (ndRad + dirTriLen) / dd;
		var sy = y2 + (y3 - y2) * (ndRad + dirTriLen) / dd;

		var trg = new Object(), dis = dirTriLen / 2;
		//
		if (sx == fx) {
			console.log("XXXX Egal");
			trg.t1X = sx + dis;
			trg.t1Y = sy;
			trg.t2X = sx - dis;
			trg.t2Y = sy;	
		} else if (sy == fy) {
			console.log("YYYY Egal");
			trg.t1X = sx;
			trg.t1Y = sy - dis;
			trg.t2X = sx;
			trg.t2Y = sy + dis;
		} else {
			var a0 = (sy - fy) / (sx - fx), b0 = sy - a0 * sx;
			var trg = edgeArcTarget(sx, sy, a0, b0, dis); 
		}

		ctx.fillStyle = "Black";
		ctx.beginPath();
		ctx.moveTo(fx, fy);
		ctx.lineTo(trg.t1X, trg.t1Y);
		ctx.lineTo(trg.t2X, trg.t2Y);
		ctx.closePath();
		ctx.fill();
	}
}

function distToEdge(x, y, a0, b0, x0, y0, x1, y1) {
	if (a0 == "nu") {
		if (y >= Math.min(y0, y1) && y <= Math.max(y0, y1)) {
			return Math.abs(x - x0);	
		}
		return maxInt;
	} else if (Math.abs(a0) < zeroLimit) {
		if (x >= Math.min(x0, x1) && x <= Math.max(x0, x1)) {
			return Math.abs(y - y0);	
		}
		return maxInt;
	}
	var	a1 = -1 / a0, b1 = y - a1 * x;
	var x2 = (b1 - b0) / (a0 - a1), y2 = a1 * x2 + b1;	

	if (x2 < Math.min(x0, x1) || x2 > Math.max(x0, x1))
		return maxInt;
	if (y2 < Math.min(y0, y1) || y2 > Math.max(y0, y1))
		return maxInt;

	return Math.sqrt(distAB(x, y, x2, y2));
}

function calcEdge(i) {
	var x0 = nodes[mapNd[edges[i].first]].posX;
	var y0 = nodes[mapNd[edges[i].first]].posY;
	var x1 = nodes[mapNd[edges[i].second]].posX;
	var y1 = nodes[mapNd[edges[i].second]].posY;
	var mx = (x0 + x1) / 2, my = (y0 + y1) / 2;
	if (x0 > x1) {
		var c = x0, x0 = x1, x1 = c;
		c = y0, y0 = y1, y1 = c;
	}
	if (x1 != x0) {
		var a0 = (y1 - y0) / (x1 - x0);
		var b0 = y0 - x0 * a0;	
	} else {
		var a0 = "nu";
		var b0 = "nu";
	}
	var minD = maxInt, id = -1;
	for (var j = 0; j < nodeCnt; j++) {
		if (j == mapNd[edges[i].first])	continue;
		if (j == mapNd[edges[i].second]) continue;

		var dd = distToEdge(nodes[j].posX, nodes[j].posY, a0, b0, x0, y0, x1, y1);	
		if (dd < minD) {
			minD = dd;
			id = j;	
		}
	}
	var trg = edgeArcTarget(mx, my, a0, b0, 2 * ndRad + 2 * edDistErr);

	if (edges[i].arc != 0) {
		var d1 = distAB(edges[i].trdX, edges[i].trdY, trg.t1X, trg.t1Y);
		var d2 = distAB(edges[i].trdX, edges[i].trdY, trg.t2X, trg.t2Y);
		if (d1 <= d2)	edges[i].arc = 1;
		else	edges[i].arc = 2;	
	}
	if (minD < ndRad + edDistErr && id != -1) {
		if (edges[i].prc == 0) {
			d1 = distAB(nodes[id].posX, nodes[id].posY, trg.t1X, trg.t1Y);
			d2 = distAB(nodes[id].posX, nodes[id].posY, trg.t2X, trg.t2Y);
			edges[i].arc = (d1 <= d2) ? 2 : 1;	
		}
	} else {
		if (edges[i].prc == 1)	edges[i].arc = 0;
	}
	if (edges[i].arc == 0) {
		if (edges[i].prc > 0)	edges[i].prc -= edgePrcIncr;
		if (edges[i].prc < 0)	edges[i].prc = 0;
	} else {
		if (edges[i].prc < 1)	edges[i].prc += edgePrcIncr;
		if (edges[i].prc > 1)	edges[i].prc = 1;	
	}
	var tX, tY;	
	if (edges[i].arc == 0) {
		var d1 = distAB(edges[i].trdX, edges[i].trdY, trg.t1X, trg.t1Y);
		var d2 = distAB(edges[i].trdX, edges[i].trdY, trg.t2X, trg.t2Y);
		if (d1 < d2) {
			tX = trg.t1X;
			tY = trg.t1Y;	
		} else {
			tX = trg.t2X;
			tY = trg.t2Y;
		}
	}
	else if (edges[i].arc == 1) {
		tX = trg.t1X;
		tY = trg.t1Y;
	} else {
		tX = trg.t2X;
		tY = trg.t2Y;
	}
	edges[i].trdX = mx + edges[i].prc * (tX - mx);
	edges[i].trdY = my + edges[i].prc * (tY - my);
}

function updateMousePos(evt) {
	var rect = cnv.getBoundingClientRect();
	var scaleX = cnv.width / rect.width;
	var scaleY = cnv.height / rect.height;
	mX = (evt.clientX - rect.left) * scaleX;
	mY = (evt.clientY - rect.top) * scaleY;
}

function fixAll() {
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].fix = 1;
	}
}
function unfixAll() {
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].fix = 0;
	}
}

function hideInpBox() {
	for (var i = 0; i < nodeCnt; i++) {
		if (nodes[i].type == 1) {
			nodes[i].type = 0;
			nodes[i].name = inpBox.value;
		}
	}
	inpBox.className = "canvasInput hidden";	
	graphInputUpdate();
}

function hitEnterEsc(event) {
	if (event.keyCode == 13 || event.keyCode == 27) {
		if (graphMode == "edit") {
			hideInpBox();
		}
	}
}

function mouseDown() {
	time = 0;
 	console.log("AM PUS JOS " + mX + " " + mY);
	if (graphMode == "gravity") {
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 1;
				return;
			}
		return;
	}
	if (graphMode == "edit") {
		hideInpBox();
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 1;
				return;
			}
		return;
	}
}

function clickNode() {
  console.log("AM FACUT UN CLICK   TIMPUL: " + time);
	if (graphMode == "gravity") {
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 0;
				if (time < clickTime) {
					if (nodes[i].fix == 0)	nodes[i].fix = 1;
					else if (nodes[i].fix == 1)	nodes[i].fix = 0;
				}
				return;
			}
		return;
	}
	if (graphMode == "edit") {
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 0;			
				if (time < clickTime) {
					nodes[i].type = 1;
					inpBox.className = "canvasInput";
					inpBox.value = nodes[i].name;
					inpBox.focus();
					inpBox.select();
				}
				return;
			}
		return;
	}
} 

function mouseLeaveCnv() {
	console.log("mouse Leave");
	time = clickTime;
	clickNode();
	var dd = $("#inputBox").is(":hover");
	console.log("este? : " + dd);
	if (graphMode == "edit" && !dd) hideInpBox();
}

function forceNC(i) {
	var d = distAB(nodes[i].posX, nodes[i].posY, cx, cy);
	var dx = Math.abs(nodes[i].posX - cx);
	var dy = Math.abs(nodes[i].posY - cy);

	if (d == 0)	d = 10;
	var ax = Math.sqrt(d) * ncF;

	if (dx) {
		var m = Math.abs((nodes[i].posY - cy) / (nodes[i].posX - cx));
		var c = Math.sqrt(ax * ax / (m * m + 1));
		nodes[i].vX += c * (nodes[i].posX < cx ? 1 : -1);  
		nodes[i].vY += m * c * (nodes[i].posY < cy ? 1 : -1);
	} else {
		nodes[i].vY += ax * (nodes[i].posY < cy ? 1 : -1);
	}
}

function forceNN(i, j) { 	
	var d = distAB(nodes[i].posX, nodes[i].posY, nodes[j].posX, nodes[j].posY);	
	var dx = Math.abs(nodes[i].posX - nodes[j].posX);
	var dy = Math.abs(nodes[i].posY - nodes[j].posY);
	
	if (d == 0) {
		nodes[i].vX += -5 + Math.random() * 10;	
		nodes[i].vY += -5 + Math.random() * 10;	
		return;
	}
	var ax = ndRad * ndRad * nnF / d / d;

	if (dx) {
		var m = Math.abs((nodes[i].posY - nodes[j].posY) / (nodes[i].posX - nodes[j].posX)); 
		var c = Math.sqrt(ax * ax / (m * m + 1));
		nodes[i].vX += c * -(nodes[i].posX < nodes[j].posX ? 1 : -1);
		nodes[i].vY += m * c * -(nodes[i].posY < nodes[j].posY ? 1 : -1);
	} else {
		nodes[i].vY += ax * -(nodes[i].posY < nodes[j].posY ? 1 : -1);
	}
}

function forceEd(i, j) {
	var d = distAB(nodes[i].posX, nodes[i].posY, nodes[j].posX, nodes[j].posY);	
	var dx = Math.abs(nodes[i].posX - nodes[j].posX);
	
	var ddif = d - edgeIdealLength * edgeIdealLength;
	if (ddif == 0)	d = 1;

	var ax = edF * Math.sqrt(Math.abs(ddif));
	var sg = (ddif > 0 ? 1 : -1);

	if (dx) {
		var m = Math.abs((nodes[i].posY - nodes[j].posY) / (nodes[i].posX - nodes[j].posX));
		var c = Math.sqrt(ax * ax / (m * m + 1));
		nodes[i].vX += sg * c * (nodes[i].posX < nodes[j].posX ? 1 : -1);
		nodes[i].vY += sg * m * c * (nodes[i].posY < nodes[j].posY ? 1 : -1);
	} else {
		nodes[i].vY += sg * ax * (nodes[i].posY < nodes[j].posY ? 1 : -1);
	}
}

function checkGoAnim() {
	for (var i = 0; i < nodeCnt; i++) {
		var dd = distAB(0, 0, nodes[i].vX, nodes[i].vY); 
		if (dd > fErr) {
			return true;
		}
	}
	return false;
}

function updateNodePos(i) {
	if (nodes[i].grab == 0 && graphMode == "edit")	return;
	if (nodes[i].grab == 1) {
		nodes[i].posX = mX;
		nodes[i].posY = mY;
	}
	else if (nodes[i].fix == 0) {
		nodes[i].posX += +nodes[i].vX;
		nodes[i].posY += +nodes[i].vY;
	}
	if (nodes[i].posX > cnvSz - ndRad)	{
		nodes[i].posX = cnvSz - ndRad;
		nodes[i].vX = 0;
	}
	if (nodes[i].posY > cnvSz - ndRad) {
		nodes[i].posY = cnvSz - ndRad;
		nodes[i].vY = 0;
	}
	if (nodes[i].posX < ndRad) {
		nodes[i].posX = ndRad;
		nodes[i].vX = 0;
	}
	if (nodes[i].posY < ndRad) {
		nodes[i].posY = ndRad;
		nodes[i].vY = 0;
	}
}

function calcNodeVect() {
	for (var i = 0; i < nodeCnt; i++) {
		forceNC(i);
		for (var j = 0; j < nodeCnt; j++)
			if (i != j) {
				forceNN(i, j);
			}
	}
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].second == undefined)	continue;
		forceEd(mapNd[edges[i].first], mapNd[edges[i].second]); 			
		forceEd(mapNd[edges[i].second], mapNd[edges[i].first]); 			
	}
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].vX *= dragRate;
		nodes[i].vY *= dragRate;
	
		if (Math.abs(nodes[i].vX) > maxVel || Math.abs(nodes[i].vY) > maxVel) {
			var m = maxVel / Math.max(Math.abs(nodes[i].vX), Math.abs(nodes[i].vY));
			nodes[i].vX *= m;
			nodes[i].vY *= m;	
		}
	}
}

function drawGraph() {
	
	ctx.clearRect(0, 0, cnv.width, cnv.height);	
	ctx.font = "30px Monospace";
	ctx.textAlign = "center";
	ctx.textBaseline = "middle";	
	ctx.lineWidth = lineWidth;	
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].second == undefined)	continue;

		calcEdge(i);
		var x0 = nodes[mapNd[edges[i].first]].posX;
		var y0 = nodes[mapNd[edges[i].first]].posY;
		var x1 = nodes[mapNd[edges[i].second]].posX;
		var y1 = nodes[mapNd[edges[i].second]].posY;
		
		drawEdgeArc(i, x0, y0, edges[i].trdX, edges[i].trdY, x1, y1);
	}

	ctx.font = "30px Monospace";
	ctx.textAlign = "center";
	ctx.textBaseline = "middle";	

	for (var i = 0; i < nodeCnt; i++) {
		ctx.lineWidth = arcLineWidth;
		if (nodes[i].fix == 1)	ctx.lineWidth = thickArcLineWidth;

		ctx.beginPath();
		ctx.arc(nodes[i].posX, nodes[i].posY, ndRad, 0, 2 * Math.PI);	
		ctx.stroke();	
		var str = document.getElementById("nodeBackColor").value;
		ctx.fillStyle = str;
		ctx.fill();

		if (nodes[i].type == 0) {
			ctx.fillStyle = document.getElementById("nodeColor").value;
			ctx.fillText(nodes[i].name, nodes[i].posX, nodes[i].posY);
		}
		if (nodes[i].type == 1) {
			updateInputBox(nodes[i].posX, nodes[i].posY);
		}
	}
}

function startAnimate() {
	fpsInterval = 1000 / FPS;
	then = Date.now();
	animate();
}

function animate() {
	//if (!checkGoAnim() && ct > 1)	return; 
	requestAnimationFrame(animate);
	
	now = Date.now();
	elapsed = now - then;

	if (elapsed > fpsInterval) {
		then = now - (elapsed % fpsInterval);
			
		calcNodeVect();
		ct++;
  	//console.log("end " + ct);
		for (var i = 0; i < nodeCnt; i++) {
			updateNodePos(i);
		}
//	console.log("AM DESENAT");	
		drawGraph();
	}
}

function addNode(id) {
	console.log("addNode " + id);
	if (nodes[id] == undefined) { 
		nodes[id] = new Object();
		nodes[id].posX = Math.random() * cnvSz;
		nodes[id].posY = Math.random() * cnvSz;
	}
	nodes[id].vX = 0;
	nodes[id].vY = 0;	
}

function updateGraphData() {
	console.log("updateGraphData");
	var txt = document.getElementById("graphData").value;
	newEdges = [];
	newNodes = [];
	mapNd = {};

	var eC = 0, nC = 0, nrCnt = 0, str = "";
	newEdges[eC] = new Object();	
	for (var i = 0; i < txt.length; i++) {
		if (txt[i] != ' ' && txt[i] != '\n') {
			str += txt[i];
		}
		if (txt[i] == ' ' || i + 1 == txt.length || txt[i] == '\n') {
			if (str.length) {
				nrCnt++;
				if (nrCnt == 1) {
					newEdges[eC].first = str;
				}
				if (nrCnt == 2) {
					newEdges[eC].second = str;
				}
				if (nrCnt == 3) {
					newEdges[eC].leng = str;
				}
				if (nrCnt <= 2 && mapNd[str] == undefined) {
					mapNd[str] = nC;
					newNodes[nC] = str;
					nC++;
				}
				str = "";
			}
			if ((txt[i] == '\n' || i + 1 == txt.length) && nrCnt) {
				eC++;
				newEdges[eC] = new Object();
				nrCnt = 0;
			}
		}
	}
	if (newEdges[eC].first != undefined)	eC++;
	
	console.log("nodeCnt " + nodeCnt);
	console.log("nodeCnt " + nC);
	var k = 0;
	for (var i = 0; i < nodeCnt; i++) {
		var ok = 0;
		for (var j = 0; j < nC; j++)
			if (nodes[i].name == newNodes[j]) {
				ok = 1;
				break;
			}
		if (ok) {
			swapNodes(k, i);
			k++;
		}
	}
	for (var i = 0; i < nC; i++) {
		var ok = 0;
		for (var j = 0; j < nodeCnt; j++)
			if (newNodes[i] == nodes[j].name) {
				ok = 1;
				break;
			}
		if (!ok) {
			addNode(k);
			nodes[k].name = newNodes[i];
			k++;	
		}
	}
	for (var i = 0; i < eC; i++) {
		if (edges[i] == undefined)	edges[i] = new Object();
		edges[i].first = newEdges[i].first;
		edges[i].second = newEdges[i].second;
		edges[i].leng = newEdges[i].leng;
		if (edges[i].arc == undefined)	edges[i].arc = 0;
		if (edges[i].prc == undefined)	edges[i].prc = 0;
		if (edges[i].trdX == undefined)	edges[i].trdX = 0;
		if (edges[i].trdY == undefined)	edges[i].trdY = 0;
	}
	for (var i = 0; i < nC; i++) {
		nodes[i].vX = 0;
		nodes[i].vY = 0;
		nodes[i].grab = 0;
		nodes[i].type = 0;
		mapNd[nodes[i].name] = i;
		if (nodes[i].fix == undefined)	nodes[i].fix = 0;
	}
	if (nodeCnt > nC) {
		for (var i = nC; i < nodeCnt; i++) {
			nodes[i].fix = 0;
		}
	}
	if (edgeCnt > eC) {
		for (var i = eC; i < edgeCnt; i++) {
			edges[i].prc = 0;
			edges[i].arc = 0;
			edges[i].trdX = 0;
			edges[i].trdY = 0;
		}
	}

	nodeCnt = nC;
	edgeCnt = eC;
	
	console.log("am modificat datele grafului");	
	console.log("noduri si mucii \n");
	console.log(nodeCnt + '\n');	
	console.log(edgeCnt + '\n');	
	console.log("hsi sa vedem muchiiile");
	for (var i = 0; i < edgeCnt; i++) {
		console.log(edges[i].first + ' ' + edges[i].second + ' ' + edges[i].leng);	
	} 
	console.log("hai sa vedem nodurile");
	for (var i = 0; i < nodeCnt; i++) {
		console.log(nodes[i].name + " " + nodes[i].posX + " " + nodes[i].posY + " " + nodes[i].vX + " " + nodes[i].vY);
	}
	document.getElementById("nodeCount").value = nodeCnt;

	ct = 0;
	console.log("started animation");
	startAnimate();

	console.log("END updateGraphData");
}

function updateNodeSize() {
	var str = document.getElementById("nodeSize").value;	
	if (isNumber(str) && str.length > 0)
		ndRad = str;
	if (ndRad > cnvSz / 2)
		ndRad = cnvSz / 2;
	if (ndRad <= 0)
		ndRad = 1;
	if (str.length > 0)
		document.getElementById("nodeSize").value = ndRad;
	
	ndRad *= 1;
	drawGraph();
}

function updateEdgeIdealLength() {
	var str = document.getElementById("edgeLength").value;

	if (isNumber(str))
		edgeIdealLength = str;
	if (edgeIdealLength > cnvSz && str.length > 0)
		edgeIdealLength = cnvSz;
	if (edgeIdealLength <= 0)
		edgesIdealLength = 1;
	if (str.length > 0)
		document.getElementById("edgeLength").value = edgeIdealLength;
	
	edgeIdealLength *= 1;
	drawGraph();
}

function hideAllTabs() {
	document.getElementById("gravityTab").className = "gravityTab hidden";
	document.getElementById("editTab").className = "editTab hidden";
	document.getElementById("inputBox").className = "canvasInput hidden";
	document.getElementById("pathTab").className = "pathTab hidden";
	document.getElementById("highlightTab").className = "highlightTab hidden";
	document.getElementById("sortTab").className = "sortTab hidden";
	document.getElementById("configTab").className = "configTab hidden";
}
function selectPaths() {
	hideAllTabs();
	document.getElementById("pathTab").className = "pathTab";
}
function selectHighLight() {
	hideAllTabs();
	document.getElementById("highlightTab").className = "highlightTab";
}
function selectSort() {
	hideAllTabs();
	document.getElementById("sortTab").className = "sortTab";
}
function selectConfig() {
	hideAllTabs();
	document.getElementById("configTab").className = "configTab";
}
function selectGravity() {
	graphMode = "gravity";
	hideAllTabs();
	document.getElementById("gravityTab").className = "gravityTab";
}
function selectEdit() {
	graphMode = "edit";
	hideAllTabs();
	document.getElementById("editTab").className = "editTab";
	inpBox = document.getElementById("inputBox");
}




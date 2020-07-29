// Parses the development applications at the South Australian Municipal Council of Roxby Downs
// web site and places them in a database.
//
// Michael Bone
// 5th March 2019

"use strict";

import * as cheerio from "cheerio";
import * as request from "request-promise-native";
import * as sqlite3 from "sqlite3";
import * as urlparser from "url";
import * as moment from "moment";
import * as pdfjs from "pdfjs-dist";

sqlite3.verbose();

const DevelopmentApplicationsSearchUrl = "https://www.roxbydowns.sa.gov.au/search?collection=roxby-downs-council-meta&query=%22development+register%22&start_rank=1&num_ranks=200";
const CommentUrl = "mailto:roxby@roxbycouncil.com.au";

declare const process: any;

// Two points that are less than the tolerance apart will be considered the same point.

const Tolerance = 3;

// Sets up an sqlite database.

async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text)");
            resolve(database);
        });
    });
}

// Inserts a row in the database if the row does not already exist.

async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or replace into [data] values (?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate
        ], function(error, row) {
            if (error) {
                console.error(error);
                reject(error);
            } else {
                console.log(`    Saved application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\" and received date \"${developmentApplication.receivedDate}\" to the database.`);
                sqlStatement.finalize();  // releases any locks
                resolve(row);
            }
        });
    });
}

// A 2D point.

interface Point {
    x: number,
    y: number
}

// A bounding rectangle.

interface Rectangle {
    x: number,
    y: number,
    width: number,
    height: number
}

// An element (consisting of text and intersecting cells) in a PDF document.

interface Element extends Rectangle {
    text: string
}

// A cell in a grid (owning zero, one or more elements).

interface Cell extends Rectangle {
    elements: Element[]
}

// Constructs a rectangle based on the intersection of the two specified rectangles.

function intersect(rectangle1: Rectangle, rectangle2: Rectangle): Rectangle {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}

// Calculates the fraction of an element that lies within a cell (as a percentage).  For example,
// if a quarter of the specifed element lies within the specified cell then this would return 25.

function getPercentageOfElementInCell(element: Element, cell: Cell) {
    let elementArea = getArea(element);
    let intersectionArea = getArea(intersect(cell, element));
    return (elementArea === 0) ? 0 : ((intersectionArea * 100) / elementArea);
}

// Calculates the area of a rectangle.

function getArea(rectangle: Rectangle) {
    return rectangle.width * rectangle.height;
}

// Gets the percentage of horizontal overlap between two rectangles (0 means no overlap and 100
// means 100% overlap).

function getHorizontalOverlapPercentage(rectangle1: Rectangle, rectangle2: Rectangle) {
    if (rectangle1 === undefined || rectangle2 === undefined)
        return 0;

    let startX1 = rectangle1.x;
    let endX1 = rectangle1.x + rectangle1.width;

    let startX2 = rectangle2.x;
    let endX2 = rectangle2.x + rectangle2.width;

    if (startX1 >= endX2 || endX1 <= startX2 || rectangle1.width === 0 || rectangle2.width === 0)
        return 0;

    let intersectionWidth = Math.min(endX1, endX2) - Math.max(startX1, startX2);
    let unionWidth = Math.max(endX1, endX2) - Math.min(startX1, startX2);

    return (intersectionWidth * 100) / unionWidth;
}

// Examines all the lines in a page of a PDF and constructs cells (ie. rectangles) based on those
// lines.

async function parseCells(page) {
    let operators = await page.getOperatorList();

    // Find the lines.  Each line is actually constructed using a rectangle with a very short
    // height or a very narrow width.

    let lines: Rectangle[] = [];

    let previousRectangle = undefined;
    let transformStack = [];
    let transform = [ 1, 0, 0, 1, 0, 0 ];
    transformStack.push(transform);

    for (let index = 0; index < operators.fnArray.length; index++) {
        let argsArray = operators.argsArray[index];

        if (operators.fnArray[index] === pdfjs.OPS.restore)
            transform = transformStack.pop();
        else if (operators.fnArray[index] === pdfjs.OPS.save)
            transformStack.push(transform);
        else if (operators.fnArray[index] === pdfjs.OPS.transform)
            transform = pdfjs.Util.transform(transform, argsArray);
        else if (operators.fnArray[index] === pdfjs.OPS.constructPath) {
            let argumentIndex = 0;
            for (let operationIndex = 0; operationIndex < argsArray[0].length; operationIndex++) {
                if (argsArray[0][operationIndex] === pdfjs.OPS.moveTo)
                    argumentIndex += 2;
                else if (argsArray[0][operationIndex] === pdfjs.OPS.lineTo)
                    argumentIndex += 2;
                else if (argsArray[0][operationIndex] === pdfjs.OPS.rectangle) {
                    let x1 = argsArray[1][argumentIndex++];
                    let y1 = argsArray[1][argumentIndex++];
                    let width = argsArray[1][argumentIndex++];
                    let height = argsArray[1][argumentIndex++];
                    let x2 = x1 + width;
                    let y2 = y1 + height;
                    [x1, y1] = pdfjs.Util.applyTransform([x1, y1], transform);
                    [x2, y2] = pdfjs.Util.applyTransform([x2, y2], transform);
                    width = x2 - x1;
                    height = y2 - y1;
                    previousRectangle = { x: x1, y: y1, width: width, height: height };
                }
            }
        } else if ((operators.fnArray[index] === pdfjs.OPS.fill || operators.fnArray[index] === pdfjs.OPS.eoFill) && previousRectangle !== undefined) {
            lines.push(previousRectangle);
            previousRectangle = undefined;
        }
    }

    // Determine all the horizontal lines and vertical lines that make up the grid.  The following
    // is careful to ignore the short lines and small rectangles that could make up vector images
    // outside of the grid (such as a logo).  Otherwise these short lines would cause problems due
    // to the additional cells that they would cause to be constructed later.

    let points: Point[] = [];

    for (let line of lines) {
        let startPoint: Point = undefined;
        let endPoint: Point = undefined;

        if (line.height <= Tolerance && line.width >= 10) {
            // Identify a horizontal line.  Extract its start and end points.

            startPoint = { x: line.x, y: line.y };
            endPoint = { x: line.x + line.width, y: line.y };
        } else if (line.width <= Tolerance && line.height >= 10) {
            // Identify a vertical line (note that these might not be very tall if there are not
            // many development applications in the grid).  Extract its start and end points.

            startPoint = { x: line.x, y: line.y };
            endPoint = { x: line.x, y: line.y + line.height };
        }

        // Record the points for later processing.

        if (endPoint !== undefined && startPoint !== undefined) {
            if (!points.some(point => (startPoint.x - point.x) ** 2 + (startPoint.y - point.y) ** 2 < Tolerance ** 2))
                points.push(startPoint);
            if (!points.some(point => (endPoint.x - point.x) ** 2 + (endPoint.y - point.y) ** 2 < Tolerance ** 2))
                points.push(endPoint);    
        }
    }

    // Construct cells based on the grid of points.

    let cells: Cell[] = [];
    for (let point of points) {
        // Find the next closest point in the X direction (moving across horizontally with
        // approximately the same Y co-ordinate).

        let closestRightPoint = points.reduce(((previous, current) => (Math.abs(current.y - point.y) < Tolerance && current.x > point.x && (previous === undefined || (current.x - point.x < previous.x - point.x))) ? current : previous), undefined);

        // Find the next closest point in the Y direction (moving down vertically with
        // approximately the same X co-ordinate).

        let closestDownPoint = points.reduce(((previous, current) => (Math.abs(current.x - point.x) < Tolerance && current.y > point.y && (previous === undefined || (current.y - point.y < previous.y - point.y))) ? current : previous), undefined);

        // Construct a rectangle from the discovered points.

        if (closestRightPoint !== undefined && closestDownPoint !== undefined)
            cells.push({ elements: [], x: point.x, y: point.y, width: closestRightPoint.x - point.x, height: closestDownPoint.y - point.y });
    }

    // Sort the cells by approximate Y co-ordinate and then by X co-ordinate.

    let cellComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
    cells.sort(cellComparer);
    return cells;
}

// Parses the text elements from a page of a PDF.

async function parseElements(page) {
    let textContent = await page.getTextContent();

    // Find all the text elements.

    let elements: Element[] = textContent.items.map(item => {
        let transform = item.transform;

        // Work around the issue https://github.com/mozilla/pdf.js/issues/8276 (heights are
        // exaggerated).  The problem seems to be that the height value is too large in some
        // PDFs.  Provide an alternative, more accurate height value by using a calculation
        // based on the transform matrix.

        let workaroundHeight = Math.sqrt(transform[2] * transform[2] + transform[3] * transform[3]);

        let x = transform[4];
        let y = transform[5];
        let width = item.width;
        let height = workaroundHeight;

        return { text: item.str, x: x, y: y, width: width, height: height };
    });

    return elements;
}

// Parses a PDF document.

async function parsePdf(url: string) {
    console.log(`Reading development applications from ${url}.`);

    let developmentApplications = [];

    // Read the PDF.

    let buffer = await request({ url: url, encoding: null, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);

    // Parse the PDF.  Each page has the details of multiple applications.

    let applicationNumberHeadingCell: Cell = undefined;
    let receivedDateHeadingCell: Cell = undefined;
    let addressHeadingCell: Cell = undefined;
    let descriptionHeadingCell: Cell = undefined;

    let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
    for (let pageIndex = 0; pageIndex < pdf.numPages; pageIndex++) {
        console.log(`Reading and parsing applications from page ${pageIndex + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(pageIndex + 1);

        // Construct cells (ie. rectangles) based on the horizontal and vertical line segments
        // in the PDF page.

        let cells = await parseCells(page);

        // Construct elements based on the text in the PDF page.

        let elements = await parseElements(page);

        // The co-ordinate system used in a PDF is typically "upside down" so invert the
        // co-ordinates (and so this makes the subsequent logic easier to understand).

        for (let cell of cells)
            cell.y = -(cell.y + cell.height);

        for (let element of elements)
            element.y = -(element.y + element.height);

        // Sort the cells by approximate Y co-ordinate and then by X co-ordinate.

        let cellComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
        cells.sort(cellComparer);

        // Sort the text elements by approximate Y co-ordinate and then by X co-ordinate.

        let elementComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
        elements.sort(elementComparer);

        // Allocate each element to an "owning" cell.

        for (let element of elements) {
            let ownerCell = cells.find(cell => getPercentageOfElementInCell(element, cell) > 50);  // at least 50% of the element must be within the cell deemed to be the owner
            if (ownerCell !== undefined)
                ownerCell.elements.push(element);
        }

        // Group the cells into rows.

        let rows: Cell[][] = [];
        for (let cell of cells) {
            let row = rows.find(row => Math.abs(row[0].y - cell.y) < Tolerance);  // approximate Y co-ordinate match
            if (row === undefined)
                rows.push([ cell ]);  // start a new row
            else
                row.push(cell);  // add to an existing row
        }

        // Check that there is at least one row (even if it is just the heading row).

        if (rows.length === 0) {
            let elementSummary = elements.map(element => `[${element.text}]`).join("");
            console.log(`No development applications can be parsed from the current page because no rows were found (based on the grid).  Elements: ${elementSummary}`);
            continue;
        }

        // Ensure the rows are sorted by Y co-ordinate and that the cells in each row are sorted
        // by X co-ordinate (this is really just a safety precaution because the earlier sorting
        // of cells in the parseCells function should have already ensured this).

        let rowComparer = (a, b) => (a[0].y > b[0].y) ? 1 : ((a[0].y < b[0].y) ? -1 : 0);
        rows.sort(rowComparer);

        let rowCellComparer = (a, b) => (a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0);
        for (let row of rows)
            row.sort(rowCellComparer);

        // Find the heading cells.

        if (applicationNumberHeadingCell === undefined) {
            applicationNumberHeadingCell = cells.find(cell => cell.elements.some(element => element.text.toLowerCase().replace(/\s/g, "") === "app"));
            receivedDateHeadingCell = cells.find(cell => cell.elements.some(element => element.text.toLowerCase().replace(/\s/g, "") === "lodged"));
            addressHeadingCell = cells.find(cell => cell.elements.some(element => element.text.toLowerCase().replace(/\s/g, "") === "siteaddress"));
            descriptionHeadingCell = cells.find(cell => cell.elements.some(element => element.text.toLowerCase().replace(/\s/g, "") === "description"));
            if (descriptionHeadingCell === undefined)
                descriptionHeadingCell = cells.find(cell => cell.elements.some(element => element.text.toLowerCase().replace(/\s/g, "") === "developmentdescription"));
        }

        if (applicationNumberHeadingCell === undefined) {
            let elementSummary = elements.map(element => `[${element.text}]`).join("");
            console.log(`No development applications can be parsed from the current page because the "App Number" column heading was not found.  Elements: ${elementSummary}`);
            continue;
        }

        if (addressHeadingCell === undefined) {
            let elementSummary = elements.map(element => `[${element.text}]`).join("");
            console.log(`No development applications can be parsed from the current page because the "Site Address" column heading was not found.  Elements: ${elementSummary}`);
            continue;
        }

        // Try to extract a development application from each row (some rows, such as the heading
        // row, will not actually contain a development application).

        for (let row of rows) {
            let applicationNumberCell = row.find(cell => getHorizontalOverlapPercentage(cell, applicationNumberHeadingCell) > 90);
            let receivedDateCell = row.find(cell => getHorizontalOverlapPercentage(cell, receivedDateHeadingCell) > 90);
            let addressCell = row.find(cell => getHorizontalOverlapPercentage(cell, addressHeadingCell) > 90);
            let descriptionCell = row.find(cell => getHorizontalOverlapPercentage(cell, descriptionHeadingCell) > 90);

            // Construct the application number.

            if (applicationNumberCell === undefined)
                continue;
            let applicationNumber = applicationNumberCell.elements.map(element => element.text).join("").trim();
            if (!/[0-9]+\/[0-9]+\/[0-9]+/.test(applicationNumber))  // an application number must be present, for example, "690/006/15"
                continue;
            console.log(`Found development application ${applicationNumber}.`);

            // Construct the address.

            if (addressCell === undefined) {
                console.log("Ignoring the development application because it has no address cell.");
                continue;
            }

            let address = addressCell.elements.map(element => element.text).join("").replace(/\s\s+/g, " ").trim();

            if (address === "") {
                console.log("Ignoring the development application because it has no address.");
                continue;
            } 

            if (address === "") {  // an address must be present
                console.log("Ignoring the development application because the address is blank.");
                continue;
            }

            // Construct the description.

            let description = "";
            if (descriptionCell !== undefined)
                description = descriptionCell.elements.map(element => element.text).join("").replace(/\s\s+/g, " ").trim();

            // Construct the received date.

            let receivedDate = moment.invalid();
            if (receivedDateCell !== undefined && receivedDateCell.elements.length > 0)
                receivedDate = moment(receivedDateCell.elements.map(element => element.text).join("").replace(/\s\s+/g, " ").trim(), "D MMMM YYYY", true);

            developmentApplications.push({
                applicationNumber: applicationNumber,
                address: address,
                description: ((description === "") ? "No Description Provided" : description),
                informationUrl: url,
                commentUrl: CommentUrl,
                scrapeDate: moment().format("YYYY-MM-DD"),
                receivedDate: receivedDate.isValid() ? receivedDate.format("YYYY-MM-DD") : ""
            });        
        }
    }

    return developmentApplications;
}

// Gets a random integer in the specified range: [minimum, maximum).

function getRandom(minimum: number, maximum: number) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}

// Pauses for the specified number of milliseconds.

function sleep(milliseconds: number) {
    return new Promise(resolve => setTimeout(resolve, milliseconds));
}

// Parses the development applications.

async function main() {
    // Ensure that the database exists.

    let database = await initializeDatabase();

    // Search for pages containing development application PDFs.

    console.log(`Retrieving page: ${DevelopmentApplicationsSearchUrl}`);

    let body = await request({ url: DevelopmentApplicationsSearchUrl, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);

    let pdfPageUrls: string[] = [];
    for (let element of $("p.noLeading a.uGoToLink").get()) {
        let pdfPageUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsSearchUrl).href;
        if (!pdfPageUrl.toLowerCase().includes(".pdf"))
            if (!pdfPageUrls.some(url => url === pdfPageUrl))  // avoid duplicates
                pdfPageUrls.push(pdfPageUrl);
    }

    // Randomly select two pages that contain developmnet application PDFs (avoid processing all
    // PDFs at once because this may use too much memory, resulting in morph.io terminating the
    // current process).

    let selectedPdfPageUrls: string[] = [];
    if (pdfPageUrls.length > 0) {
        selectedPdfPageUrls.push(...pdfPageUrls.splice(getRandom(0, pdfPageUrls.length), 1));
        selectedPdfPageUrls.push(...pdfPageUrls.splice(getRandom(0, pdfPageUrls.length), 1));
    }

    if (selectedPdfPageUrls.length === 0) {
        console.log("No PDF URLs were found.");
        return;
    }

    // Read the page containing development applications.

    for (let selectedPdfPageUrl of selectedPdfPageUrls) {
        console.log(`Retrieving page: ${selectedPdfPageUrl}`);

        // Find any PDFs on the page.

        let body = await request({ url: selectedPdfPageUrl, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
        await sleep(2000 + getRandom(0, 5) * 1000);
        let $ = cheerio.load(body);
    
        let pdfUrls: string[] = [];
        for (let element of $("li.result-item a").get()) {
            let pdfUrl = new urlparser.URL(element.attribs.href, selectedPdfPageUrl).href;
            if (pdfUrl.toLowerCase().includes(".pdf"))
                if (!pdfUrls.some(url => url === pdfUrl))  // avoid duplicates
                    pdfUrls.push(pdfUrl);
        }

        // Parse the PDFs that were found (there will typically only be one).

        for (let pdfUrl of pdfUrls) {
            console.log(`Parsing document: ${pdfUrl}`);
            let developmentApplications = await parsePdf(pdfUrl);
            console.log(`Parsed ${developmentApplications.length} development ${(developmentApplications.length == 1) ? "application" : "applications"} from document: ${pdfUrl}`);
            
            // Attempt to avoid reaching 512 MB memory usage (this will otherwise result in the
            // current process being terminated by morph.io).
    
            if (global.gc)
                global.gc();
    
            console.log("Inserting development applications into the database.");
            for (let developmentApplication of developmentApplications)
                await insertRow(database, developmentApplication);
        }
    }
}

main().then(() => console.log("Complete.")).catch(error => console.error(error));

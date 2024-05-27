import {
    Constant,
    Err,
    Middleware,
    Req,
    Res,
    ResponseErrorObject,
} from "@tsed/common";
import { Env } from "@tsed/core";
import { Exception } from "@tsed/exceptions";

const toHTML = (message = "") => message.replace(/\n/gi, "<br />");

function getErrors(error: any) {
    return [error, error.origin]
        .filter(Boolean)
        .reduce((errs, { errors }: ResponseErrorObject) => {
            return [...errs, ...(errors || [])];
        }, []);
}

function getHeaders(error: any) {
    return [error, error.origin]
        .filter(Boolean)
        .reduce((obj, { headers }: ResponseErrorObject) => {
            return {
                ...obj,
                ...(headers || {}),
            };
        }, {});
}

@Middleware()
export class GlobalErrorHandlerMiddleware {
    @Constant("env")
    env: Env | undefined;

    use(@Err() error: any, @Req() request: Req, @Res() response: Res): any {
        if (typeof error === "string") {
            response.status(404).send(toHTML(error));

            return;
        }

        if (error instanceof Exception || error.status) {
            this.handleException(error, request, response);

            return;
        }

        this.handleError(error, request, response);

        return;
    }

    protected handleError(error: any, request: Req, response: Res) {
        const logger = request.$ctx.logger;
        const err = this.mapError(error);

        logger.error({
            error: err,
        });

        response
            .set(getHeaders(error))
            .status(err.status)
            .json(this.env === Env.PROD ? "InternalServerError" : err);
    }

    protected handleException(error: any, request: Req, response: Res) {
        const logger = request.$ctx.logger;
        const err = this.mapError(error);
        logger.error({
            error: err,
        });

        response.set(getHeaders(error)).status(error.status).json(err);
    }

    protected mapError(error: any) {
        return {
            message: error.message,
            stack: this.env === Env.DEV ? error.stack : undefined,
            status: error.status || 500,
            origin: {
                ...(error.origin || {}),
                errors: undefined,
            },
            errors: getErrors(error),
        };
    }
}

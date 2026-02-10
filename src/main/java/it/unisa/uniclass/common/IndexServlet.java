package it.unisa.uniclass.common;

import it.unisa.uniclass.utenti.model.Utente;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

@WebServlet(name = "indexServlet", value = "/Home")
public class IndexServlet extends HttpServlet {

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) {
        try {
            HttpSession session = request.getSession(false);

            Utente user = (session != null)
                    ? (Utente) session.getAttribute("currentSessionUser")
                    : null;

            if (user == null) {
                response.sendRedirect("Login.jsp");
                return;
            }

            request.getRequestDispatcher("index.jsp").forward(request, response);

        } catch (Exception e) {
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (Exception ignored) {}
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) {
        doGet(request, response);
    }
}

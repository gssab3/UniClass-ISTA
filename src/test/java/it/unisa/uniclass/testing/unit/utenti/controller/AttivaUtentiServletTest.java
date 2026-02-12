package it.unisa.uniclass.testing.unit.utenti.controller;

import it.unisa.uniclass.utenti.controller.AttivaUtentiServlet;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Tipo;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.mockito.Mockito.*;

class AttivaUtentiServletTest {

    // Sottoclasse per rendere pubblici i metodi protetti e usare il costruttore con service mockato
    static class TestableAttivaUtentiServlet extends AttivaUtentiServlet {
        public TestableAttivaUtentiServlet(AccademicoService service) {
            super(service);
        }
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) {
            super.doGet(req, resp);
        }
        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) {
            super.doPost(req, resp);
        }
    }

    private TestableAttivaUtentiServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private AccademicoService accademicoService;

    @BeforeEach
    void setUp() throws IOException {
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        accademicoService = mock(AccademicoService.class);

        // usa sempre il costruttore con service mockato
        servlet = new TestableAttivaUtentiServlet(accademicoService);

        when(request.getContextPath()).thenReturn("/ctx");
        when(request.getServletContext()).thenReturn(mock(jakarta.servlet.ServletContext.class));

        // Configure sendRedirect to not throw IOException
        doNothing().when(response).sendRedirect(anyString());
    }

    @Test
    void testAddSuccess() throws IOException {
        when(request.getParameter("param")).thenReturn("add");
        when(request.getParameter("email")).thenReturn("test@unisa.it");
        when(request.getParameter("matricola")).thenReturn("12345");
        when(request.getParameter("tipo")).thenReturn("Studente");

        Accademico acc = mock(Accademico.class);
        when(acc.getEmail()).thenReturn("test@unisa.it");
        when(acc.getMatricola()).thenReturn("12345");
        when(acc.getTipo()).thenReturn(Tipo.Studente);

        when(accademicoService.trovaEmailUniClass("test@unisa.it")).thenReturn(acc);
        when(accademicoService.trovaAccademicoUniClass("12345")).thenReturn(acc);

        servlet.doPost(request, response);

        verify(acc).setAttivato(true);
        verify(accademicoService).aggiungiAccademico(acc);
        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp");
    }

    @Test
    void testAddErrorTipoDiverso() throws IOException {
        when(request.getParameter("param")).thenReturn("add");
        when(request.getParameter("email")).thenReturn("test@unisa.it");
        when(request.getParameter("matricola")).thenReturn("12345");
        when(request.getParameter("tipo")).thenReturn("Docente");

        Accademico acc = mock(Accademico.class);
        when(acc.getEmail()).thenReturn("test@unisa.it");
        when(acc.getMatricola()).thenReturn("12345");
        when(acc.getTipo()).thenReturn(Tipo.Studente);

        when(accademicoService.trovaEmailUniClass("test@unisa.it")).thenReturn(acc);
        when(accademicoService.trovaAccademicoUniClass("12345")).thenReturn(acc);

        servlet.doPost(request, response);

        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp?action=error");
    }

    @Test
    void testAddErrorAccademicoNull() throws IOException {
        when(request.getParameter("param")).thenReturn("add");
        when(request.getParameter("email")).thenReturn("test@unisa.it");
        when(request.getParameter("matricola")).thenReturn("12345");
        when(request.getParameter("tipo")).thenReturn("Studente");

        when(accademicoService.trovaEmailUniClass("test@unisa.it")).thenReturn(null);
        when(accademicoService.trovaAccademicoUniClass("12345")).thenReturn(null);

        servlet.doPost(request, response);

        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp?action=error");
    }

    @Test
    void testRemoveSuccess() throws IOException {
        when(request.getParameter("param")).thenReturn("remove");
        when(request.getParameter("email-remove")).thenReturn("test@unisa.it");

        Accademico acc = mock(Accademico.class);
        when(accademicoService.trovaEmailUniClass("test@unisa.it")).thenReturn(acc);

        servlet.doPost(request, response);

        verify(accademicoService).cambiaAttivazione(acc, false);
        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp");
    }

    @Test
    void testRemoveAccademicoNull() throws IOException {
        when(request.getParameter("param")).thenReturn("remove");
        when(request.getParameter("email-remove")).thenReturn("test@unisa.it");

        when(accademicoService.trovaEmailUniClass("test@unisa.it")).thenReturn(null);

        servlet.doPost(request, response);

        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp");
    }

    @Test
    void testDoGetDelegatesToDoPost() throws IOException {
        when(request.getParameter("param")).thenReturn("remove");
        when(request.getParameter("email-remove")).thenReturn("test@unisa.it");

        servlet.doGet(request, response);

        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp");
    }

    @Test
    void testDoPostPublicDelegatesToDoPost() throws IOException {
        when(request.getParameter("param")).thenReturn("remove");
        when(request.getParameter("email-remove")).thenReturn("test@unisa.it");

        servlet.doPostPublic(request, response);

        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp");
    }

    @Test
    void testDoPostWithUnknownParam() {
        when(request.getParameter("param")).thenReturn("altro");

        servlet.doPost(request, response);

        // non fa nulla, ma serve per coprire il ramo
        verifyNoInteractions(accademicoService);
    }

}

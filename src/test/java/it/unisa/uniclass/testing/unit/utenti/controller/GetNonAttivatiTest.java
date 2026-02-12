package it.unisa.uniclass.testing.unit.utenti.controller;

import it.unisa.uniclass.utenti.controller.GetNonAttivati;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Tipo;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class GetNonAttivatiTest {

    // Sottoclasse per rendere pubblici i metodi protetti
    static class TestableGetNonAttivati extends GetNonAttivati {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) {
            super.doGet(req, resp);
        }

        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) {
            super.doPost(req, resp);
        }
    }

    private TestableGetNonAttivati servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private StringWriter stringWriter;
    private PrintWriter printWriter;

    @BeforeEach
    void setUp() throws IOException {
        servlet = new TestableGetNonAttivati();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);

        stringWriter = new StringWriter();
        printWriter = new PrintWriter(stringWriter);
        when(response.getWriter()).thenReturn(printWriter);
        when(request.getServletContext()).thenReturn(mock(jakarta.servlet.ServletContext.class));
    }

    @Test
    void testDoGetWithNonEmptyList() throws Exception {
        List<Accademico> lista = new ArrayList<>();
        Accademico acc = mock(Accademico.class);
        when(acc.getEmail()).thenReturn("test@unisa.it");       // String
        when(acc.getMatricola()).thenReturn("12345");           // String
        when(acc.getTipo()).thenReturn(Tipo.Docente);           // enum Tipo
        lista.add(acc);

        try (MockedConstruction<AccademicoService> mocked = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaAttivati(false)).thenReturn(lista))) {

            servlet.doGet(request, response);

            String output = stringWriter.toString();
            assertTrue(output.contains("test@unisa.it"));
            assertTrue(output.contains("12345"));
            assertTrue(output.contains("Docente")); // enum serializzato come stringa
            verify(response).setContentType("application/json");
            verify(response).setCharacterEncoding("UTF-8");
        }
    }

    @Test
    void testDoGetWithEmptyList() throws Exception {
        try (MockedConstruction<AccademicoService> mocked = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaAttivati(false)).thenReturn(new ArrayList<>()))) {

            servlet.doGet(request, response);

            String output = stringWriter.toString().trim();
            assertEquals("[]", output);
        }
    }

    @Test
    void testDoPostDelegatesToDoGet() throws Exception {
        List<Accademico> lista = new ArrayList<>();
        Accademico acc = mock(Accademico.class);
        when(acc.getEmail()).thenReturn("post@unisa.it");
        when(acc.getMatricola()).thenReturn("67890");
        when(acc.getTipo()).thenReturn(Tipo.PersonaleTA);
        lista.add(acc);

        try (MockedConstruction<AccademicoService> mocked = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaAttivati(false)).thenReturn(lista))) {

            servlet.doPost(request, response);

            String output = stringWriter.toString();
            assertTrue(output.contains("post@unisa.it"));
            assertTrue(output.contains("67890"));
            assertTrue(output.contains("PersonaleTA"));
        }
    }
}

package it.unisa.uniclass.testing.unit.utenti.service;

import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.PersonaleTA;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import it.unisa.uniclass.testing.utils.TestUtils; // Utility per dati dinamici
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.MockitoAnnotations;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class UtenteServiceTest {

    static class TestableUtenteService extends UtenteService {
        public PersonaleTAService exposePersonaleTAService() {
            return super.getPersonaleTAService();
        }
        public AccademicoService exposeAccademicoService() {
            return super.getAccademicoService();
        }
    }

    @Mock
    private PersonaleTAService personaleTAService;

    @Mock
    private AccademicoService accademicoService;

    private UtenteService utenteService;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        utenteService = new UtenteService();
        utenteService.setPersonaleTAService(personaleTAService);
        utenteService.setAccademicoService(accademicoService);
    }

    // --- retrieveByEmail ---
    @Test
    void testRetrieveByEmail_PersonaleTAPresente() {
        PersonaleTA pta = new PersonaleTA();
        pta.setEmail("pta@unisa.it");

        when(personaleTAService.trovaEmail("pta@unisa.it")).thenReturn(pta);

        Utente result = utenteService.retrieveByEmail("pta@unisa.it");

        assertNotNull(result);
        assertEquals("pta@unisa.it", result.getEmail());
    }

    @Test
    void testRetrieveByEmail_AccademicoPresente() {
        Accademico acc = new Accademico();
        acc.setEmail("acc@unisa.it");

        when(personaleTAService.trovaEmail("acc@unisa.it")).thenReturn(null);
        when(accademicoService.trovaEmailUniClass("acc@unisa.it")).thenReturn(acc);

        Utente result = utenteService.retrieveByEmail("acc@unisa.it");

        assertNotNull(result);
        assertEquals("acc@unisa.it", result.getEmail());
    }

    @Test
    void testRetrieveByEmail_Null() {
        when(personaleTAService.trovaEmail("unknown@unisa.it")).thenReturn(null);
        when(accademicoService.trovaEmailUniClass("unknown@unisa.it")).thenReturn(null);

        Utente result = utenteService.retrieveByEmail("unknown@unisa.it");
        assertNull(result);
    }

    // --- retrieveByUserAndPassword ---
    @Test
    void testRetrieveByUserAndPassword_PersonaleTACorretta() throws AuthenticationException {
        String dynamicPassword = TestUtils.generateTestPassword();
        PersonaleTA pta = new PersonaleTA();
        pta.setEmail("pta@unisa.it");
        pta.setPassword(dynamicPassword); // Rimosso hardcoding

        when(personaleTAService.trovaEmail("pta@unisa.it")).thenReturn(pta);

        Utente result = utenteService.retrieveByUserAndPassword("pta@unisa.it", dynamicPassword);
        assertNotNull(result);
        assertEquals("pta@unisa.it", result.getEmail());
    }

    @Test
    void testRetrieveByUserAndPassword_AccademicoCorretta() throws AuthenticationException {
        String dynamicPassword = TestUtils.generateTestPassword();
        Accademico acc = new Accademico();
        acc.setEmail("acc@unisa.it");
        acc.setPassword(dynamicPassword); // Rimosso hardcoding

        when(personaleTAService.trovaEmail("acc@unisa.it")).thenReturn(null);
        when(accademicoService.trovaEmailUniClass("acc@unisa.it")).thenReturn(acc);

        Utente result = utenteService.retrieveByUserAndPassword("acc@unisa.it", dynamicPassword);
        assertNotNull(result);
        assertEquals("acc@unisa.it", result.getEmail());
    }

    @Test
    void testRetrieveByUserAndPassword_PasswordErrata() {
        String correctPassword = TestUtils.generateTestPassword();
        String wrongPassword = correctPassword + "_WRONG";

        PersonaleTA pta = new PersonaleTA();
        pta.setEmail("pta@unisa.it");
        pta.setPassword(correctPassword);

        when(personaleTAService.trovaEmail("pta@unisa.it")).thenReturn(pta);

        assertThrows(AuthenticationException.class, () ->
                utenteService.retrieveByUserAndPassword("pta@unisa.it", wrongPassword));
    }

    @Test
    void testRetrieveByUserAndPassword_NessunoTrovato() throws AuthenticationException {
        when(personaleTAService.trovaEmail("unknown@unisa.it")).thenReturn(null);
        when(accademicoService.trovaEmailUniClass("unknown@unisa.it")).thenReturn(null);

        Utente result = utenteService.retrieveByUserAndPassword("unknown@unisa.it", "any");
        assertNull(result);
    }

    @Test
    void testSetters() {
        PersonaleTAService mockPTA = mock(PersonaleTAService.class);
        AccademicoService mockAcc = mock(AccademicoService.class);

        utenteService.setPersonaleTAService(mockPTA);
        utenteService.setAccademicoService(mockAcc);

        assertNotNull(utenteService);
    }

    @Test
    void testLazyLoadingPersonaleTAServiceSafe() {
        try (MockedConstruction<PersonaleTAService> mocked = mockConstruction(PersonaleTAService.class)) {
            TestableUtenteService service = new TestableUtenteService();
            PersonaleTAService result = service.exposePersonaleTAService();
            assertNotNull(result);
        }
    }

    @Test
    void testRetrieveByUserAndPassword_NoResultException() throws AuthenticationException {
        when(personaleTAService.trovaEmail("x@unisa.it")).thenThrow(new NoResultException());

        Utente result = utenteService.retrieveByUserAndPassword("x@unisa.it", "pwd");
        assertNull(result);
    }

    @Test
    void testRetrieveByUserAndPassword_AccademicoPasswordErrata() {
        String correctPassword = TestUtils.generateTestPassword();
        String wrongPassword = correctPassword + "_WRONG";

        Accademico acc = new Accademico();
        acc.setEmail("acc@unisa.it");
        acc.setPassword(correctPassword);

        when(personaleTAService.trovaEmail("acc@unisa.it")).thenReturn(null);
        when(accademicoService.trovaEmailUniClass("acc@unisa.it")).thenReturn(acc);

        assertThrows(AuthenticationException.class, () ->
                utenteService.retrieveByUserAndPassword("acc@unisa.it", wrongPassword));
    }

    @Test
    void testLazyLoadingAccademicoServiceSafe() {
        try (MockedConstruction<AccademicoService> mocked = mockConstruction(AccademicoService.class)) {
            TestableUtenteService service = new TestableUtenteService();
            AccademicoService result = service.exposeAccademicoService();
            assertNotNull(result);
        }
    }
}